/*@
  requires x >= 0;
  ensures  (x == 42 ==> \result == 999) && (x != 42 ==> \result == 2);
*/
int f(int x) {
  int y = 0;
  /*@ requires x >= 0;
      ensures  (x == 42 ==> \false) && (x != 42 ==> y == 2);
      returns  (x != 42 ==> \false) && (x == 42 ==> y == 1 && \result == 5);
      assigns  y;
  */
  {
    if (x == 42) { y = 1; return 5; }
    y = 2;
  }
  return y;
}

int main() {
  int r = f(42);
  return 0;
}
