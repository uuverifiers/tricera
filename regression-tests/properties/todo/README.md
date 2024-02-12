Stack pointers in functions are currently not fully supported by TriCera, and the stack pointer tests as a result do not currently work - both true and false versions will return "UNSAFE", as they are modelled (incorrectly) using the theory of heaps.

valid-deref-type-1-false.c
No distinction is made between int and long in default settings, and it seems this also does not work using machine integer semantics. This should be fixed.

valid-deref-type-2-false.c and valid-deref-type-2-true.c
No distinction is made between int and long in default settings, and it seems this also does not work using machine integer semantics (throws an error). This should be fixed.