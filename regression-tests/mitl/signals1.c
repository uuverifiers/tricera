
signal p;
signal q;

thread A {
  assume(p && q);
  assert(p); // SAFE
  assert(q);
}
