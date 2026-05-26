
int x = 0;

thread A {
  clock c = 0;
  progress (x > 0) {}
  assert(c == 0); // SAFE
}

