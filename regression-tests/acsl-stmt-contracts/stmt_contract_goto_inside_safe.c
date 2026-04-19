int main() {
  int x = 0;
  /*@ requires x == 0;
      ensures  x == 1;
  */
  {
    goto skip;
    x = 99;
    skip: x = 1;
  }
  //@ assert x == 1;
  return 0;
}
