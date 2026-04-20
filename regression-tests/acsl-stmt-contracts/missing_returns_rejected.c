int f(int x) {
  int y = 0;
  /*@ requires x >= 0;
      ensures  y == 1;
  */
  {
    if (x == 42) { y = 1; return 5; }
    y = 1;
  }
  return y;
}

int main() {
  f(0);
  return 0;
}
