int main() {
  int x = 7;
  /*@ requires x == 7;
      ensures  x == 8;
      assigns  \nothing;
  */
  { x = 8; }
  //@ assert x == 8;
  return 0;
}
