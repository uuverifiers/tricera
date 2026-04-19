int foo(int x) {
  int r = x;
  /*@ requires x >= 0 && r == x;
      ensures  r == 99;
      returns  \true;
      assigns  r;
  */
  { if (x == 0) return 99; }
  return r;
}

int main() {
  foo(5);
  return 0;
}
