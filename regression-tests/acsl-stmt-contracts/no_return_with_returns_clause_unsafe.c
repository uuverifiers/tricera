int bar(int x) {
  int r = x;
  /*@ requires x == 10 && r == 10;
      ensures  r == 11;
      returns  \result == 999;
      assigns  r;
  */
  { r = r + 1; }
  return r;
}

int main() {
  int y = bar(10);
  //@ assert y == 12;
  return 0;
}
