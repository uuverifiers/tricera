
signal p;

int x = 5;

thread A {
  clock c = 0;
  progress (c <= 10) {}
  assume(c == 10);
  assert(p); // UNSAFE
}

thread C {
  assume(p == (x > 0));
  progress (p == (x > 0)) {
    assume(0);
  }
}
