void foo() {
  int i;
  /*@ loop invariant 0 <= i; */
  for (i = 0; i < 3; ++i) {}
}
