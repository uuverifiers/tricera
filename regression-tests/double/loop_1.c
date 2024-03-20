//SAFE
void main(void) {
  int i = 0;
  double x = 0.5;
  double y = x;
  while (x < 3000.0) {
    x = x*2.0;
    y = x;
    ++i;
  }
  assert(x==y);
}
