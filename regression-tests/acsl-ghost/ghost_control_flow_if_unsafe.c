//@ ghost int v;

int main(int x) {
  /*@ ghost if (x > 0) v = 1; else v = 2; */
  //@ assert v == 1;
  return 0;
}
