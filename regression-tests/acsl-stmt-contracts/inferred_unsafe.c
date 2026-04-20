int main() {
  int x = 5;
  /*@ contract @*/
  { x = x + 1; }
  //@ assert x == 10;
  return 0;
}
