// A ghost block that interleaves a local ghost declaration with an
// assignment to a pre-existing ghost global.
//@ ghost int x;

int main() {
  /*@ ghost int y = 5;
             x = y + 1;
  */
  //@ assert x == 6;
  //@ assert y == 5;
  return 0;
}
