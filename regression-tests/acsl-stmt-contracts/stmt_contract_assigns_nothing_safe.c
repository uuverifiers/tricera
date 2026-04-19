int main() {
  int x = 7;
  /*@ requires x == 7;
      ensures  x == 7;
      assigns  \nothing;
  */
  { int tmp = x; }
  //@ assert x == 7;
  return 0;
}
