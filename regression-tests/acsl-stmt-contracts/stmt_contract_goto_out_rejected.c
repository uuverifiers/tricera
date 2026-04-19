int main() {
  int x = 0;
  /*@ requires x == 0;
      ensures  x == 1;
  */
  {
    goto outside;
    x = 1;
  }
outside:
  return 0;
}
