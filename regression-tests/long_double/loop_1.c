void main(void) {
  int i = 0;
  long double x = 0.5l;
  long double y = x;
  while (x < 3000.0l) {
    x = x*2.0l;
    y = x;
    ++i;
  }
  assert(x==y);
}
