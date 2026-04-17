//@ ghost int x;

int main() {
  /*@ ghost x = 1;
             x = x + 1;
  */
  //@ assert x == 99;
  return 0;
}
