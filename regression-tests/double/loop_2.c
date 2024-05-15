//UNSAFE
int N = _;

void main(void) {
  int i = 0;
  double x = 0.5;
  double y = x;
  while (i < N) {
    if(x == y) {
        x = x+2.25;
    }
    ++i;
  }
  assert(x==y);
}
