
int x;

thread A {
  clock c;
  c = 0;

  progress (c <= 2) {
    x = x + 1;
  }
}

thread B {
  clock d;
  int y;

  d = 0;
  progress (1) {}
  assume(d > 1);

  y = x;
  progress (1) {}
  assert(x == y); // SAFE
}
