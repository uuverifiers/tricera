void foo(void) {
  int a = -7;
  //@ assert -7 / 2 == -3 && -7 % 2 == -1;
  //@ assert a / 2 == -3 && a % 2 == -1;
}
