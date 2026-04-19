int main() {
  int a = 1;
  int b = 2;
  /*@ contract @*/
  {
    a = a + b;
    b = b * 2;
  }
  //@ assert a == 3;
  //@ assert b == 4;
  return 0;
}
