int main() {
  int x = 0;
  int flag = 1;
  /*@ requires flag == 1 && x == 0;
      ensures  x == 42;
  */
  if (flag) x = 42; else x = -1;
  //@ assert x == 42;
  return 0;
}
