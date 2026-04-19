int f(int x) {
  int y = 0;
  /*@ requires x >= 0;
      ensures  y == 1;
      returns  y == 1 && \result == 5;
  */
  {
    if (x == 42) { y = 1; return 5; }
    y = 1;
  }
  return y;
}

int main() {
  f(42);
  f(0);
  return 0;
}
