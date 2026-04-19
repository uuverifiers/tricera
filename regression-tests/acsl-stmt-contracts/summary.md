# ACSL statement contracts in TriCera — Phases A, B, C summary and audit

Written as an internal review of what's landed. The aim: make the
design decisions and the invariants they rely on explicit, so future
work can build on them rather than patch around them.

## What is landed

ACSL 1.23 §2.6.3 statement contracts — a `requires / ensures / assigns`
contract attached to a statement or a block — are verified and inferred
end-to-end. The use-site is encoded modularly: the body lives in a
background-axiom subsystem and the caller carries only a pre-check
assertion plus a post-assume continuation. The solver therefore
verifies each body once against its own contract, not re-inlined at
every use.

```c
int main() {
  int r = 0;
  /*@ requires r >= 0 && r <= 1000;
      ensures  r == \old(r) + 1;
      assigns  r;
  */
  { r = r + 1; }
  //@ assert r >= 1 && r <= 1001;
  return 0;
}
```

And the inference form:

```c
int main() {
  int x = 5;
  /*@ contract @*/
  { x = x + 1; }
  //@ assert x == 6;
  return 0;
}
```

TriCera prints:

```
/* statement contract at 3:3 */
/*@
  requires x == 5;
  ensures x == 6 && \old(x) == 5;
*/
```

## Design decisions, with the alternatives considered

### One abstraction, not two

Function and statement contracts share `funToContract`,
`funToPreAtom`, `funToPostAtom`, `prePredsToReplace`, `postPredsToReplace`,
and the encoder that rewrites atoms in those sets. The alternative —
a separate `stmtContracts` / `stmtPredsToReplace` / second encoder pass
— would have meant double bookkeeping and a second place to add every
new encoder feature. One pipeline means one audit and one place to
evolve.

### `ContractOldStorage(contractName, originalName)` on `VariableStorage`

Old-snapshot variables are Tricera-internal bookkeeping. Before Phase A
they shared storage with the real variable they shadowed (`v.storage`),
and protecting a function's own old-snapshots from being mutated by a
nested statement contract required a runtime lookup through
`functionPostOldArgs`. That patch leaked function-level knowledge into
the statement-contract code.

After Phase A, any old-snapshot carries `ContractOldStorage`, and a
single filter (`v.storage.isInstanceOf[ContractOldStorage]`) expresses
"this var is bookkeeping, not user state". Nested contracts work by
construction: the inner region's `visibleVars` skip the outer's
old-snapshots, the use-site uses identity rather than fresh post-terms
for them, and the outer `\old` semantics is preserved without any
per-site conditional.

### Sidecar registry instead of widening `FunctionInvariants`

Only the printer needs to distinguish a function contract from a
statement contract in its header ("contract for foo" vs "statement
contract at L:C"). Widening the `FunctionInvariants` case class — a 6th
field — would have touched ~15 files across the backtranslator (every
pattern match on `FunctionInvariants(id, …)`). Instead, CCReader owns a
`statementContractSrcInfos : Map[String, SourceInfo]` registry populated
in `translateContractedStm`, and `ResultPrinters.printACSL(registry)`
dispatches on registry membership. One field on CCReader, one curried
parameter, zero case-class churn. If we ever need the target type
further upstream we can promote it.

The Phase B plan originally called for a `ContractTarget`
(`FunctionTarget` / `StatementTarget`) ADT threaded through
`FunctionInvariants`. That ADT lived briefly in
`ccreader/ContractedRegion.scala` before being retired in favour of the
sidecar; the file was removed in the final pre-review pass. Reviewers
who remember seeing it in earlier commits will find no live reference
now — everything flows through `statementContractSrcInfos`.

### User-annotated vs inference anchor — behaviour split

For a user-annotated contract we populate
`funToContract`, `prePredsToReplace`, `postPredsToReplace`, and
`funsWithAnnot`. The encoder then rewrites the generated pre/post atoms
into `false :- entry, !pre` and `body &&& assigns`.

For `/*@ contract @*/` we leave those four sets alone. The pre/post
predicates stay uninterpreted; the solver finds them. `funsWithAnnot`
membership then decides `FunctionInvariants.isSrcAnnotated`, which
gates `FunctionInvariantsFilter(i => !i.isSrcAnnotated)` in Main —
user-annotated contracts are filtered out of the ACSL output (we don't
echo back what the user wrote), inferred ones are printed.

One code path, one split in registration. Matches function-contract
inference exactly.

### Body scope: push/pop with a bare-decl restriction

The old-snapshots live in a pushed `LocalVars` frame. `popFrame` at the
end of `translateContractedStm` removes them. But it would also remove
any variables the body itself declared if the body is a bare
declaration (e.g. `/*@ … */ int y = 0;`) — those should survive the
span per C scoping. Rather than special-case DecS inside the body, the
translator rejects it with

```
A statement contract's body must not be a bare declaration;
wrap it in a compound statement.
```

A compound statement (`{ int y = 0; x = y; }`) pushes its own frame and
pops it before we pop ours, so inner declarations get the right scope.
Regression covered by `stmt_contract_bare_decl_rejected.c` and
`stmt_contract_inner_local_safe.c`.

### Body clauses are a subsystem

During body translation the main clause and assertion buffers are
swapped out, so everything emitted during the body lands in
`functionClauses[contractName]`. At system assembly this list rolls
into `backgroundAxioms`. The body is therefore a self-contained Horn
subsystem keyed on the generated name. The main process keeps only the
caller-side pre-assertion and the post-continuation — the modular
verification payoff. `try/finally` guarantees the buffers are
restored and the frame popped even if body translation throws.

### Jumps inside the body are fine; jumps out are rejected

`break` / `continue`: the check fires only when
`innermostLoopExit == contractOuterLoopExit` — i.e. the targeted loop
is the same one that existed before we entered the span. A break to
a loop nested inside the body keeps working because the loop's
preds are pushed and popped by `withinLoop`. Covered by
`stmt_contract_break_inside_safe.c`,
`stmt_contract_continue_inside_safe.c`,
`stmt_contract_break_out_rejected.c`.

`goto`: labels are resolved by `connectJumps` after the enclosing
function is translated. Solution: snapshot `labelledLocs` and
`jumpLocs` sizes at body entry; after body translation, any `goto`
whose target label was not added inside the body is rejected, and
the rest are resolved into the body's subsystem right there. The
enclosing function's `connectJumps` pass never sees them — this is
essential because the body lives in background axioms and the
enclosing function's goto-bridging expects all preds to live in its
own process. Covered by `stmt_contract_goto_inside_safe.c` and
`stmt_contract_goto_out_rejected.c`.

Generalising the escape case for `break` / `continue` / `goto` would
mean the same cross-subsystem forwarding that escaping `return` needs
(one forwarding clause per loop / label target). The hornconcurrency
constraint — a predicate can't be defined in both a process and a
background — is the blocker. Deferred as follow-up; the intra-body
variants cover real-world usage.

### Heap through the model, not the theory

Before Phase A, `StmtContractContext.getHeapTerm` pattern-matched on
`HeapTheoryModel` to grab `m.heapVar`. That hard-coded one of two heap
models into the statement-contract code path. Phase A routes through
`HeapModel.getACSL{Pre,Post}StateHeapTerm(this)` — the existing
abstraction function contracts already use — and catches
`NotImplementedError` from `InvariantEncodingsModel` with a clear
translation error. When that model grows ACSL hooks, statement
contracts light up for it without a TriCera change.

## Corner cases and what's tested for each

| Corner case                                                | Test                                              | Verdict |
|------------------------------------------------------------|---------------------------------------------------|---------|
| Basic block body                                            | `stmt_contract_block_safe.c`                      | SAFE    |
| Body violates ensures                                       | `stmt_contract_block_unsafe.c`                    | UNSAFE  |
| Single-statement body                                       | `stmt_contract_single_stm_safe.c`                 | SAFE    |
| `if`/`else` as the contracted statement                     | `stmt_contract_if_body_safe.c`                    | SAFE    |
| Pre violated at use site                                    | `stmt_contract_pre_violated_unsafe.c`             | UNSAFE  |
| `assigns` with a listed location                            | `stmt_contract_assigns_unsafe.c`                  | UNSAFE  |
| `assigns \nothing;`                                         | `stmt_contract_assigns_nothing_safe.c`            | SAFE    |
| `\old` of a scalar                                          | `stmt_contract_old_safe.c`                        | SAFE    |
| `\old` of a struct field                                    | `stmt_contract_old_struct_safe.c` + unsafe        | both    |
| `\old` of a global                                          | `stmt_contract_old_global_safe.c`                 | SAFE    |
| `\old` of a heap deref                                      | `stmt_contract_heap_old_safe.c`                   | SAFE    |
| Heap assigns, listed vs unlisted modification               | `stmt_contract_heap_assigns_{safe,unsafe}.c`      | both    |
| Heap contract violated                                      | `stmt_contract_heap_ensures_unsafe.c`             | UNSAFE  |
| Two adjacent contracts in the same block                    | `stmt_contract_nested_safe.c`                     | SAFE    |
| Contract inside a block that holds another contract         | `stmt_contract_nested_in_body_safe.c`             | SAFE    |
| Body declares a local in its inner block                    | `stmt_contract_inner_local_safe.c`                | SAFE    |
| Ghost operations inside the body                            | `stmt_contract_ghost_inside_safe.c`               | SAFE    |
| Statement contract inside a function with its own contract  | `stmt_contract_function_contract_outer_safe.c`    | SAFE    |
| `goto` whose target is inside the body                      | `stmt_contract_goto_inside_safe.c`                | SAFE    |
| `goto` whose target is outside the body                     | `stmt_contract_goto_out_rejected.c`               | rejected|
| `return` inside the body, post holds on all paths           | `stmt_contract_early_return_safe.c`               | SAFE    |
| `return` inside the body, post violated on return path      | `stmt_contract_early_return_unsafe.c`             | UNSAFE  |
| `break` to a loop inside the body                           | `stmt_contract_break_inside_safe.c`               | SAFE    |
| `continue` to a loop inside the body                        | `stmt_contract_continue_inside_safe.c`            | SAFE    |
| `break` leaving the body                                    | `stmt_contract_break_out_rejected.c`              | rejected|
| Two contract annotations back-to-back with no body between  | `stmt_contract_adjacent_rejected.c`               | rejected|
| Contract with no following statement                        | `stmt_contract_trailing_warns.c`                  | warning |
| Contract body is a bare declaration                         | `stmt_contract_bare_decl_rejected.c`              | rejected|
| Minimal form: only `ensures`                                | `stmt_contract_ensures_only_safe.c`               | SAFE    |
| Minimal form: only `requires`                               | `stmt_contract_requires_only_safe.c`              | SAFE    |
| Full form: requires + ensures + assigns + \old              | `stmt_contract_full_safe.c`                       | SAFE    |
| `/*@ contract @*/` inference                                | `stmt_contract_inferred_safe.c`                   | SAFE    |
| `return` in body of a void enclosing function, post holds   | `stmt_contract_void_return_safe.c`                | SAFE    |
| `return` in body of a void enclosing function, post fails   | `stmt_contract_void_return_unsafe.c`              | UNSAFE  |
| `return` value originates in the body (not from post formula) | `stmt_contract_return_value_in_body_safe.c`     | SAFE    |
| Body always returns, multiple return paths                  | `stmt_contract_multi_return_paths_safe.c`         | SAFE    |
| Body calls another function                                 | `stmt_contract_nested_call_safe.c`                | SAFE    |

All 36 cases run clean on every invocation of `runalldirs`; no other
suite regressed after Phases A, B, and C.

## Corner cases found and fixed during this audit

1. **Body as a bare declaration leaked scoping.** The translator now
   rejects this form explicitly. Test: `stmt_contract_bare_decl_rejected.c`.
2. **Exception during body translation orphaned the pushed frame.**
   Body translation is now wrapped in `try/finally` that restores the
   main buffers and pops the frame whether the body succeeds or
   throws. (Not directly testable from the outside, but a follow-on
   translator call would have seen a dirty scope before the fix.)
3. **`ContractedRegion` / `ContractTarget` was unreferenced.** Phase B's
   original plan threaded a `ContractTarget` ADT through the
   backtranslator; in the end the sidecar `statementContractSrcInfos`
   subsumed it. The `ContractedRegion.scala` file never had a live
   construction and was removed. Reviewers who encounter mentions in
   earlier commit messages can safely treat them as superseded.
4. **Early return in a void-returning enclosing function crashed the
   Horn translator.** The return-forwarding clause used
   `returnPred.arity - 1` as the result-slot offset, which for a void
   function drops the last formal instead of yielding an empty slot.
   Detecting the slot by name (`_res…`) turned out to miss the
   result var created for inlined functions (`_<fname>Ret`), so the
   final version compares CCVar identity against `outerVars`: a
   returnPred arg that isn't in the enclosing formals is the result.
   Tests: `stmt_contract_void_return_safe.c`,
   `stmt_contract_void_return_unsafe.c`.
5. **Return forwarding leaked the return value.** The use-site
   forwarding clause referenced `returnPostPred`, which the encoder
   rewrites into `post && assigns`. Since the contract's post formula
   doesn't mention the return value, the rewrite dropped the
   body→caller binding and the forwarded value was unconstrained —
   silently turning safe programs into UNSAFE. Fixed by pointing the
   use-site clause at `returnBodyPred` (uninterpreted, defined only
   on the return path) so the rewrite doesn't apply. The post-check
   on the return path still runs via `returnPostPred :- returnBodyPred`
   on the body side. Test: `stmt_contract_return_value_in_body_safe.c`.
6. **Fall-through continuation overapproximated.** Same structural
   issue as (5), but on the fall-through path: the use-site
   continuation referenced `postPred`, so it fired even when the body
   always returned and fall-through was unreachable. The verifier
   happily explored that dead continuation and produced spurious
   UNSAFE verdicts. Fixed by pointing the continuation at `bodyExit`
   instead; fall-through is now gated on the body actually reaching
   its end. Test: `stmt_contract_multi_return_paths_safe.c`.
7. **Contract-name collision across inlined call sites.** A function
   with a statement contract, called twice, used to produce two
   predicates both named `stmt_contract_0_pre/_post/…`. Each overwrote
   the previous entry in `funToPreAtom`/`funToPostAtom`, so the
   encoder's pre/post rewrite resolved to the wrong atom and the
   substitution that should have landed the clause-specific args in
   the pre formula silently became a no-op. Fixed by moving the
   counter from `FunctionTranslator` (reset on each inlining) to
   `CCReader` (program-wide). Test:
   `stmt_contract_multi_return_paths_safe.c` (calls `sign` three
   times).

## Boundaries of the current implementation

Deliberately rejected with a clear error:

- `break` / `continue` / `goto` that escape the contracted span.
- `return` inside a stmt contract nested inside another stmt contract,
  or inside a stmt contract whose enclosing function has an ACSL
  contract of its own. (Flat returns work in Phase C.)
- Adjacent contract annotations with no statement between them.
- Contract annotation at the end of a block with no following statement
  (warned, contract ignored).
- Bare declaration as the contract body.
- Two ACSL annotations where the second is a contract attached to the
  same span as a user assertion — would need a grammar change.

Landed in Phase C:

- `return` inside a contracted body (flat, i.e. not nested inside
  another stmt contract and enclosing function has no ACSL contract):
  a `bodyReturn` predicate catches the return; a second post
  predicate `<contract>_ret_post` (registered under `<contract>_ret`
  in `funToContract` with the same contract) is derived from
  `bodyReturn` on the body side, and the encoder rewrites it into
  `!(post && assigns)` on the body side and `post && assigns` in the
  use-site forwarding clause. The forwarding clause then lets the
  return value reach the enclosing function's return pred with the
  post condition assumed. Tests:
  `stmt_contract_early_return_safe.c`,
  `stmt_contract_early_return_unsafe.c`.

Still rejected (deliberately), will need a follow-up:

- `return` inside a stmt contract that sits inside another stmt
  contract's body. The forwarding clause would have to cross from the
  inner body's background subsystem into the outer's — the Horn
  system hornconcurrency builds rejects this cross-process reference.
- `return` inside a stmt contract whose enclosing function has its
  own ACSL contract. The function's return pred has a wider argument
  layout (function old-vars) that the forwarding clause isn't yet
  shaped to handle.

Out of scope for this feature, flagged for later:

- Escaping `break` / `continue` / `goto` — the same forwarding idea
  generalises, but each needs a tracked "escape predicate" per target,
  which is bigger than Phase C's scope.
- ACSL named behaviours (`behavior foo:`), abrupt clauses (`exits` /
  `breaks` / `continues` / `returns`), and contracts on labeled
  statements — all ACSL §2.6.3 but each is a standalone feature.
- `assigns` with array subscript syntax (`assigns a[1];`) — TriCera's
  assigns translator accepts only global identifiers and heap pointer
  dereferences. `assigns *(a + 1);` works; array-index syntax does
  not. Not specific to statement contracts.
- `InvariantEncodingsModel.getACSL{Pre,Post}StateHeapTerm` — heap-model
  side; the translator catches the `NotImplementedError` and emits a
  clear message pointing at the heap model.

## Invariants the rest of the code relies on

1. A statement-contract name is in `statementContractSrcInfos` iff it
   is also in `funToPreAtom` and `funToPostAtom` (populated together in
   `translateContractedStm`). `getStatementContractPreds` depends on
   this.
2. A statement-contract name is in `funsWithAnnot` iff it is user-
   annotated (i.e. not `/*@ contract @*/`). `ResultConverter` uses
   this to drive `isSrcAnnotated`, which in turn decides whether the
   contract is filtered out of printed output.
3. A statement-contract name is in `prePredsToReplace` and
   `postPredsToReplace` iff it is user-annotated. For inference
   anchors the solver must see the pre/post predicates uninterpreted,
   so the encoder leaves them alone.
4. Every old-snapshot CCVar created for a contract carries
   `ContractOldStorage(contractName, originalName)`. Anywhere that
   classifies in-scope vars as "user-visible" filters these out.
5. Body-internal gotos are resolved inside `translateContractedStm`
   before clauses are stashed. The enclosing function's
   `connectJumps` must never see a body-internal jump (or it would
   fail to find the target, since the body's predicates live in
   background axioms).
6. `returnPred.argVars` ends in the enclosing function's result slot
   iff the function is non-void. The slot is identified by its name
   starting with `Literals.resultExecSuffix` (`_res`), which is how
   `CCScope.getResVar` constructs it. The early-return forwarding
   clause in `translateContractedStm` uses this to size the value it
   hands to `returnPred`.

## On moving this code out of `CCReader`

Reviewer question was: CCReader is already 3700 lines, is any of this
extractable? The answer for *this branch* is: a little, and it's
already done. The bigger refactor needs its own pass.

Currently lifted out:

- `ContractOldStorage` lives in `ccreader/CCVar.scala` alongside the
  other `VariableStorage` variants.
- The statement-contract counter sits at CCReader class scope with a
  one-line rationale (must be program-wide to avoid name collisions
  when a contract-holding function is inlined more than once).
- The printer split (`ResultPrinters.printACSL`) and the source-info
  sidecar (`statementContractSrcInfos`) keep the backtranslator
  change out of CCReader.

Not lifted out, reasons in order of weight:

- `translateContractedStm` (~270 lines) touches `scope`, `heapVars`,
  `modelHeap`, the `clauses`/`assertionClauses` buffers,
  `functionClauses`/`functionAssertionClauses`, `labelledLocs`,
  `jumpLocs`, `usedJumpTargets`, `addRichClause`,
  `mkRichAssertionClause`, `newPred`, `atom`, `output`,
  `funToPreAtom`/`funToPostAtom`/`funToContract`/`funsWithAnnot`,
  `prePredsToReplace`/`postPredsToReplace`, and
  `statementContractSrcInfos`. Moving it out means either exposing
  all of that as a public CCReader API or wrapping it in a helper
  object that takes a CCReader reference. The former enlarges the
  CCReader surface; the latter just relocates the file without
  actually trimming the entanglement. Neither is a clear win without
  first thinking about which of those are really CCReader's
  responsibility.
- `RegionAnnotationContext` is only reachable through `modelHeap`,
  `heap`, `heapModel`, and the sort/getter/wrapper maps, so it has
  the same blocker on a smaller scale.
- `FunctionTranslator.insideContractBody` / `contractBodyReturn` /
  `contractOuterLoopCont` / `contractOuterLoopExit` are per-function-
  translator state; they move with FunctionTranslator, not with the
  statement-contract code.

A reasonable next step — deferred — would be to give CCReader a
narrow `TranslationContext` interface that `translateContractedStm`
and similar helpers could depend on, and then lift those helpers out
into `ccreader/StatementContracts.scala`. That's a wider refactor
that should touch function contracts and the ghost-code pipeline too
(they share most of the same CCReader surface), and the rest of
nightly should land before it.

## Review notes

A few spots where the logic is dense enough to benefit from a focused
read:

- **`translateContractedStm` in CCReader.scala.** ~250 lines, organised
  top-to-bottom as: body-form check → annotation parse → old-var
  frame → contract parse → pre/post registration → return-forwarding
  setup → body translation (in swapped-out buffers) → stash under
  generated name → use-site clauses. The try/finally around body
  translation is load-bearing — it's what keeps the pushed frame and
  buffer swap from leaking if the ACSL translator throws.
- **`canForwardReturn` in the same method.** Three conditions gate it:
  (1) the enclosing function returns, (2) the function has no ACSL
  contract, and (3) we aren't already inside a contracted body. If
  any fails, an in-body `return` is rejected by
  `translate(Jump_stm)`. The comment block above the gate spells out
  the "why".
- **`ContractOldStorage` filter in the use-site continuation clause.**
  Outer-contract old-snapshots must be read-only across a statement
  contract's span. `postTerms` reuses the pre-state term for
  `ContractOldStorage`-tagged vars; a fresh post-state constant for
  everything else. This is the seam that makes statement contracts
  nested inside function contracts work without ad-hoc bookkeeping.
- **`ResultPrinters.printACSL` curried on `stmtContractSrcs`.** The
  printer's header logic is a two-line match; everything else is
  unchanged from the function-contract path.
