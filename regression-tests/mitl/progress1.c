
thread A {
  int x = 0;
  clock c;
  c = 0;

  progress (c <= 5) {
    x = x + 1;
  }

  assume(c == 5);
  assert(x == 1);
}
