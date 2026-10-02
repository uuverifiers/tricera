// Multi-line contract using macros. Expansion must preserve line numbers.
// UNSAFE: x == HI - 1 satisfies the precondition, whose IN_RANGE invocation
// spans lines 9 and 10; the assertion on line 15 fails, and the
// counterexample must point to line 15 and name the contract's line 9.
#define LO 0
#define HI 100
#define IN_RANGE(v) ((v) >= LO && (v) <= HI)

/*@ requires IN_RANGE(
               x)
             && x < HI;
    ensures IN_RANGE(\result);
*/
int inc(int x) {
  //@ assert x != HI - 1;
  return x + 1;
}
