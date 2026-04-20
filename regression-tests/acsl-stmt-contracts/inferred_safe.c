int main() {
  int x = 5;
  /*@ contract @*/
  { x = x + 1; }
  //@ assert x == 6;
  return 0;
}
