int main() {
  int x = 0;
  /*@ requires x == 0;
      ensures  x == 3;
  */
  {
    int y = 3;
    x = y;
  }
  //@ assert x == 3;
  return 0;
}
