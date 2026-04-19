int foo(int a) {
  int x = a;
  /*@ requires x >= 0;
      ensures  x == \old(x) + 1;
      returns  x == 7 && \result == 7;
      assigns  x;
  */
  {
    x = x + 1;
    if (x == 7) return x;
  }
  return x;
}

int main() {
  int r = foo(6);
  //@ assert r == 7;
  return 0;
}
