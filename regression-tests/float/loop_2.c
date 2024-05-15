int N = _;

void main(void) {
  int i = 0;
  float x = 0.5f;
  float y = x;
  while (i < N) {
    if(x == y) {
        x = x+2.25f;
    }
    ++i;
  }
  assert(x==y);
}
