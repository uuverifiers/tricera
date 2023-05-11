int N = _;

void main(void) {
  int i = 0;
  double x = 0.5;
  double y = x;
  while (i < N) {
    x = x*2.0f;
    y = x;
    ++i;
  }
  assert(x==y+1.0f);
}
