int N = _;

void main(void) {
  int i = 0;
  long double x = 0.5l;
  long double y = x;
  while (i < N) {
    if(x == y) {
        x = x+2.25l;
    }
    ++i;
  }
  assert(x==y);
}
