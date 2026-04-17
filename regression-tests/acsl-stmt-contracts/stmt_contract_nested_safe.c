/*@ requires x >= 0;
    ensures  \result == x + 2;
*/
int bump(int x) {
  /*@ requires x >= 0;
      ensures  x == \old(x) + 1;
  */
  { x = x + 1; }
  /*@ requires x >= 1;
      ensures  x == \old(x) + 1;
  */
  { x = x + 1; }
  return x;
}

int main() {
  int r = bump(3);
  //@ assert r == 5;
  return 0;
}
