int main() {
  int x = 0;
  /*@ requires x == 0;
      ensures  x >= 1 && x <= 10;
      assigns  x;
  */
  { x = 5; }
  //@ assert x == 5;
  return 0;
}
