//@ ghost int v;

int main(int x) {
  /*@ ghost if (x > 0) v = 1; else v = 2; */
  //@ assert (x > 0 && v == 1) || (x <= 0 && v == 2);
  return 0;
}
