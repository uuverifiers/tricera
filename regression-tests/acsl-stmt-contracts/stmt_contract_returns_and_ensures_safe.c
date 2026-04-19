int maybe_ret(int x) {
  int r = x;
  /*@ requires x >= 0 && r == x;
      ensures  r == x;
      returns  x == 0 && r == 0 && \result == 42;
      assigns  r;
  */
  {
    if (x == 0) { r = 0; return 42; }
  }
  return r;
}

int main() {
  int a = maybe_ret(7);
  int b = maybe_ret(0);
  //@ assert a == 7;
  //@ assert b == 42;
  return 0;
}
