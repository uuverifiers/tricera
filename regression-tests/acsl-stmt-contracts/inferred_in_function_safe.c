int double_it(int x) {
  int r = x;
  /*@ contract @*/
  { r = r + r; }
  return r;
}

int main() {
  int y = double_it(7);
  //@ assert y == 14;
  return 0;
}
