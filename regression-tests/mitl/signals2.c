
signal p;
signal q;

thread A {
  assume(p || q);
  assert(p); // UNSAFE
  assert(q);
}
