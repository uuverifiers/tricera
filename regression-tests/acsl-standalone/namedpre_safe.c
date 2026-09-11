/*@ requires nonneg: x >= 0;
    ensures  \result == x; */
int bar(int x) { return x; }
int foo(void) { return bar(5); }
