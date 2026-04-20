int main() {
  int x = 0;
  int flag = 0;
  /*@ requires x == 0;
      ensures  x == 42;
  */
  if (flag) x = 42; else x = -1;
  //@ assert x == 42;
  return 0;
}
