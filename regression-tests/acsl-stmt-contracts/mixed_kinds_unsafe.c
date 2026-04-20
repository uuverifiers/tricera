/*@
  requires x >= 0;
  ensures  \result == x + 2;
*/
int outer(int x) {
  int y = x;
  /*@ requires y >= 0;
      ensures  y == \old(y) + 2;
  */
  {
    y = y + 1;
  }
  return y;
}

void main() { outer(3); }
