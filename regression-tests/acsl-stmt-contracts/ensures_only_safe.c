int main() {
  int x = 42;
  /*@ ensures x == 0; */
  { x = 0; }
  //@ assert x == 0;
  return 0;
}
