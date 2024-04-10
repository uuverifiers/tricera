/*$ P(int *x) $*/

void main() {
  int x = 42;
  assert(P(&x));

  int *y;
  assume(P(y));

  assert(*y == 42);
}
