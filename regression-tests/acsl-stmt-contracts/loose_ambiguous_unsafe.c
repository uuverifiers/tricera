int f(int x) {
  int y = 0;
  /*@ requires x >= 0;
      ensures  y == 2;
      returns  y == 1 && \result == 5;
      assigns  y;
  */
  {
    if (x == 42) { y = 1; return 5; }
    y = 2;
  }
  return y;
}

int main() {
  int r = f(42);
  //@ assert r == 5;
  return 0;
}
