# Summary
TriCera is a model checker for C programs, that is being developed and mainted by Uppsala University. TriCera accepts programs in a C-like language, and currently supports:
* C structs, 
* arrays, 
* stack and heap pointers (but no pointer arithmetic),
* basic heap (dynamic memory) operations including malloc, (a variant of) calloc and free,
* threads (with its own syntax),
* function contracts,

and much more. See the `.c` and `.hcc` files under [`regression-tests`](https://github.com/uuverifiers/tricera/tree/master/regression-tests) to see some examples of what it can handle.

TriCera works by encoding the input program into a set of Constrained Horn Clauses (CHCs), which include properties explicitly added to the program through `assert` and `assume` statements, but also some explicit properties such as checking the type and runtime safety of heap accesses. It then passes the generated CHCs to [Eldarica](https://github.com/uuverifiers/eldarica) for solving. This is similar to, for instance, what [JayHorn](https://jayhorn.github.io/jayhorn/) does for Java.

TriCera can also automatically generate function contracts for functions annotated wuth `/*@contract@*/`. Contracts will then be generated when the clauses can be solved. See [`regression-tests/horn-contracts`](https://github.com/uuverifiers/tricera/tree/master/regression-tests/horn-contracts) for examples. To print the contracts, `-log:3` option must be passed to the tool.

TriCera can parse [SV-Comp](https://sv-comp.sosy-lab.org/) style `.yml` property files, and output if the expected verdict matches the analysis result. The property file must have the same name as the input file except the extension (`input_files` provided in the property file is currently ignored ). [Here](https://github.com/uuverifiers/tricera/blob/master/regression-tests/horn-hcc-heap/memtrack-01.yml) is an example from the regression tests.

# Installation
Since TriCera uses sbt, compilation is quite simple: you just need sbt installed on your machine, and then type `sbt assembly` to download the compiler, all required libraries, and produce a binary of TriCera.

After compilation (or downloading a binary release), calling TriCera is normally as easy as calling

`./tri regression-tests/horn-contracts/fib.hcc`

When using a binary release, one can instead also call

`java -jar target/scala-2.*/TriCera-assembly*.jar regression-tests/horn-contracts/fib.hcc`

This currently does not work - will be updated: ~~You can use the script tri-client instead of tri in order to run TriCera in a server-client mode, which significantly speeds up processing of multiple problems.~~

A full list of options can be obtained by calling ./tri -h.
In particular, the options `-cex` can be used to show a counterexample when the program is unsafe, and `-log:n` (n in 1..3) can be used to show the solution when the program is safe.

# Try it out online
TriCera has a [web interface](http://logicrunch.it.uu.se:4096/~zafer/tricera/) where you can try it out, which also contains many examples.

# Bug reports
TriCera is under development, and bug reports are welcome!

# Related papers
* The thesis work which led to the creation of TriCera: [Extension of the ELDARICA C model checker with heap memory
](http://uu.diva-portal.org/smash/record.jsf?dswid=3650&pid=diva2%3A1373067)
* The paper presenting the underlying Horn solver: [The ELDARICA Horn Solver](https://ieeexplore.ieee.org/document/8603013)
* An extended technical report introducing the heap theory used in encoding the heap: [A Theory of Heap for Constrained Horn Clauses (Extended Technical Report)](https://arxiv.org/abs/2104.04224).
* The decision procedure for the heap theory implemented in [Princess](http://www.philipp.ruemmer.org/princess.shtml): [Reasoning in the Theory of Heap: Satisfiability and Interpolation](https://link.springer.com/chapter/10.1007%2F978-3-030-68446-4_9).
* 
# Some of the keywords TriCera accepts
* `assert(condition)`: verify that a condition holds at this point in the program.
* `assume(condition)`: assume that a condition holds.
* `atomic { stm1; stm2; ... }`: execute a block of statements atomically. 
* `atomic { assume(!lock); lock=1; }` will atomically check that lock has value 0, and then set the variable to 1.
* `within (cond) { stm1; stm2; ... }`: execute a block of statements (atomically) before cond expires. This corresponds to time invariants in Uppaal timed automata.
* `thread <name> { ... }`: statically declare a (singleton) thread.
* `thread[<id-var>] <name> { ... }`: statically declare an infinitely replicated thread.
* `clock <name>, duration <name>`: declare clocks or variables representing time periods.
* `chan <name>`: declare a binary (UPPAAL-style) communication channel, which can be used via `chan_send` and `chan_receive`.
