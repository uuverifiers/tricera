/*@
  requires x >= 0;
  ensures  \result == x + 2;
*/
int inc(int x) {
  /*@ requires x >= 0;
      ensures  x == \old(x) + 1;
  */
  { x = x + 1; }
  return x;
}

void main() { inc(3); }
