int main() {
  int a[3];
  a[0] = 5;
  a[1] = 0;
  a[2] = 0;
  /*@ contract @*/
  { a[0] = a[0] + 1; }
  //@ assert a[0] == 6;
  return 0;
}
