int main() {
  int x = 0;
  int y = 10;
  /*@ requires x == 0 && y == 10;
      ensures  x >= 1 && x <= 10;
      assigns  x;
  */
  { x = 5; }
  //@ assert x >= 1;
  //@ assert x <= 10;
  //@ assert y == 10;
  return 0;
}
