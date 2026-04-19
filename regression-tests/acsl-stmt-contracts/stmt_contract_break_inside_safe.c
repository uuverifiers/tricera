int main() {
  int x = 0;
  /*@ requires x == 0;
      ensures  x == 1;
  */
  {
    int i;
    for (i = 0; i < 10; i = i + 1) {
      x = 1;
      if (i == 3) break;
    }
  }
  //@ assert x == 1;
  return 0;
}
