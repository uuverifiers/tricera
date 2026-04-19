int main() {
  int x = 0;
  /*@ requires x == 0;
      ensures  x == 2;
  */
  {
    /*@ requires x == 0;
        ensures  x == 1;
    */
    { x = x + 1; }
    /*@ requires x == 1;
        ensures  x == 3;
    */
    { x = x + 1; }
  }
  //@ assert x == 2;
  return 0;
}
