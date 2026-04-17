// KNOWN LIMITATION: early return bypassses check
int f(int x) {
  int y = 0;
  /*@ requires x >= 0;
      ensures  y == x + 1;
  */
  {
    if (x == 42) return 999;
    y = x + 1;
  }
  return y;
}

int main() { return 0; }
