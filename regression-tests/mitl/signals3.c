signal p;

extern int nondet();

thread A {
  int x;
  assume(x >= 0);
  progress (p) {
    while (nondet())
      x++;
  }
  if (p)
    x++;
  assert(x >= 0);
}

