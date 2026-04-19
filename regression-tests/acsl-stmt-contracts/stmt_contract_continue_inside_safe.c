int main() {
  int x = 0;
  int sum = 0;
  /*@ requires x == 0 && sum == 0;
      ensures  sum == 4;
  */
  {
    int i;
    for (i = 0; i < 4; i = i + 1) {
      if (i == 2) continue;
      if (i == 0) continue;
      sum = sum + i;
    }
  }
  //@ assert sum == 4;
  return 0;
}
