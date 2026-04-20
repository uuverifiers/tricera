int main() {
  int x = 0;
  int i;
  for (i = 0; i < 10; i = i + 1) {
    /*@ requires x == 0;
        ensures  x == 1;
    */
    {
      if (i == 3) break;
      x = 1;
    }
  }
  return 0;
}
