// Same as ghost_multi_stmt_safe.c but the assertion is deliberately
// wrong to exercise the UNSAFE path.
//@ ghost int x;

int main() {
  /*@ ghost x = 1;
             x = x + 1;
  */
  //@ assert x == 99;
  return 0;
}
