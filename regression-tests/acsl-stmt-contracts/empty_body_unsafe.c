int main() {
  int x = 5;
  /*@ requires x == 5;
      ensures  x == 6;
  */
  { }
  //@ assert x == 6;
  return 0;
}
