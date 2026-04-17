int main() {
  int x = 0;
  x = x + 1;
  /*@ requires x == 1;
      ensures  x == 2;
  */
  // nothing follows — contract has no body
}
