//@ ghost integer n = 0;

int main() {
  /*@ ghost n = n + 1; */
  //@ assert n == 1;
  return 0;
}
