int main() {
  int x = 0;
  /*@ requires x == 0;
      ensures  x == 2;
  */
  { x = x + 1; }
  return 0;
}
