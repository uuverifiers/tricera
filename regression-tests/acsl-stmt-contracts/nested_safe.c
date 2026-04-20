int main() {
  int x = 3;
  /*@ requires x >= 0;
      ensures  x == \old(x) + 1;
  */
  { x = x + 1; }
  /*@ requires x >= 1;
      ensures  x == \old(x) + 1;
  */
  { x = x + 1; }
  //@ assert x == 5;
  return 0;
}
