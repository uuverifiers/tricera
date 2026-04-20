int foo(int x) {
  int r = 0;
  /*@ requires x >= 0 && r == 0;
      ensures  \false;
      returns  \true;
      assigns  r;
  */
  { r = x; return r; }
  return r;
}

int main() {
  foo(5);
  return 0;
}
