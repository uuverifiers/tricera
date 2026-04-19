int main() {
  int x = 5;
  /*@ requires x == 5;
      ensures  x == 5;
  */
  { }
  //@ assert x == 5;
  return 0;
}
