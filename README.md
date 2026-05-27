# Summary
TriCera is a model checker for C programs, that is being developed and maintained by Uppsala University. TriCera accepts programs in a C-like language, and currently supports:
* C structs, 
* arrays, 
* stack and heap pointers (but no pointer arithmetic),
* basic heap (dynamic memory) operations including malloc, (a variant of) calloc and free,
* threads (with its own syntax),
* function contracts,

and much more. See the `.c` and `.hcc` files under [`regression-tests`](https://github.com/uuverifiers/tricera/tree/master/regression-tests) to see some examples of what it can handle.

TriCera works by encoding the input program into a set of Constrained Horn Clauses (CHCs), which include properties explicitly added to the program through `assert` and `assume` statements, but also some implicit properties such as checking the type and runtime safety of heap accesses. It then passes the generated CHCs to [Eldarica](https://github.com/uuverifiers/eldarica) for solving. This is similar to, for instance, what [JayHorn](https://jayhorn.github.io/jayhorn/) does for Java.

TriCera can also automatically generate function contracts for functions annotated with `/*@contract@*/`. Contracts will then be generated when the clauses can be solved. See [`regression-tests/horn-contracts`](https://github.com/uuverifiers/tricera/tree/master/regression-tests/horn-contracts) for examples. To print the contracts, `-log:3` option must be passed to the tool.

TriCera can parse [SV-Comp](https://sv-comp.sosy-lab.org/) style [task definition](https://gitlab.com/sosy-lab/benchmarking/task-definition-format/-/tree/2.0) files and extract the properties to check from there. The property file must have the same name as the input file except the extension (`input_files` provided in the property file is currently ignored). Alternatively, the properties to check can be specified via the command-line interface - please refer to tool command-line help for supported properties. By default, TriCera attempts to verify only user-specified assertions, and the unreachability of any calls to `reach_error` function.

# Installation
Since TriCera uses sbt, compilation is quite simple: you just need sbt installed on your machine, and then type `sbt assembly` to download the compiler, all required libraries, and produce a binary of TriCera.

After compilation (or downloading a binary release), calling TriCera is normally as easy as calling

`./tri regression-tests/horn-contracts/fib.hcc`

When using a binary release, one can instead also call

`java -jar target/scala-2.*/TriCera-assembly*.jar regression-tests/horn-contracts/fib.hcc`

A full list of options can be obtained by calling ./tri -h.
In particular, the options `-cex` can be used to show a counterexample when the program is unsafe, and `-log:n` (n in 1..3) can be used to show the solution when the program is safe.

# Native Image
TriCera can be compiled into a native image using [GraalVM](https://www.graalvm.org/) for significantly faster startup times.

**Note**: Building the native image requires GraalVM 25+ for native compilation, while the base project compilation targets Java 17. Other Java versions should likely work for the base project, but older GraalVM versions may not work for native compilation. Please refer to the `.github/workflows/scala.yml` file for a working environment setup.

To build the native image:
```bash
sbt nativeImage
```
The binary will be generated at `target/native-image/TriCera`.

Once built, the standard `tri` executable script will automatically detect the presence of the native image and use it instead of the JVM version.

# Try it out online
TriCera has a [web interface](https://eldarica.org/tricera/) where you can try it out, which also contains many examples.

# Bug reports
TriCera is under development, and bug reports are welcome!

# Related papers
* The most recent paper describing TriCera: [TriCera: Verifying C Programs Using the Theory of Heaps](https://repositum.tuwien.at/handle/20.500.12708/81374)
* The thesis work which led to the creation of TriCera: [Extension of the ELDARICA C model checker with heap memory
](http://uu.diva-portal.org/smash/record.jsf?dswid=3650&pid=diva2%3A1373067)
* The paper presenting Eldarica (Horn solver back-end of TriCera): [The ELDARICA Horn Solver](https://ieeexplore.ieee.org/document/8603013)
* The paper introducing the theory of heaps TriCera uses to encode the heap: [AN SMT-LIB Theory of Heaps](http://ceur-ws.org/Vol-3185/paper1180.pdf).
* The decision procedure for the theory of heaps implemented in [Princess](http://www.philipp.ruemmer.org/princess.shtml): [Reasoning in the Theory of Heap: Satisfiability and Interpolation](https://link.springer.com/chapter/10.1007%2F978-3-030-68446-4_9).
* 
# Some of the keywords TriCera accepts
* `assert(condition)`: verify that a condition holds at this point in the program.
* `assume(condition)`: assume that a condition holds.
* `atomic { stm1; stm2; ... }`: execute a block of statements atomically. 
* `atomic { assume(!lock); lock=1; }` will atomically check that lock has value 0, and then set the variable to 1.
* `within (cond) { stm1; stm2; ... }`: execute a block of statements (atomically) before cond expires. This corresponds to time invariants in UPPAAL timed automata.
* `thread <name> { ... }`: statically declare a (singleton) thread.
* `thread[<id-var>] <name> { ... }`: statically declare an infinitely replicated thread.
* `clock <name>, duration <name>`: declare clocks or variables representing time periods.
* `chan <name>`: declare a binary (UPPAAL-style) communication channel, which can be used via `chan_send` and `chan_receive`.
