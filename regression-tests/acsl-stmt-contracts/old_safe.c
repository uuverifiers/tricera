int main() {
  int x = 5;
  /*@ requires x >= 0;
      ensures  x == \old(x) + 1;
  */
  { x = x + 1; }
  //@ assert x == 6;
  return 0;
}
