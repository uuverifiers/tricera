int main() {
  int x = 0;
  int y = 10;
  /*@ requires x == 0;
      ensures  x == 1;
      assigns  x;
  */
  { x = x + 1; y = y + 1; }
  return 0;
}
