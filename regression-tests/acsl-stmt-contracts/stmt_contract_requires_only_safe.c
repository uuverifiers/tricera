int main() {
  int x = 5;
  /*@ requires x > 0; */
  { x = x + 1; }
  return 0;
}
