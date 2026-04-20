int main() {
  int x = -1;
  /*@ requires x >= 0;
      ensures  x >= 1;
  */
  { x = x + 1; }
  return 0;
}
