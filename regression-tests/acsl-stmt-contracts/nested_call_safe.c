int inc(int x) {
  return x + 1;
}

int foo(int n) {
  int r = n;
  /*@ requires r == n;
      ensures  r == n + 1;
      assigns  r;
  */
  { r = inc(r); }
  return r;
}

int main() {
  int r = foo(5);
  //@ assert r == 6;
  return 0;
}
