/*$ P(int *x) $*/

void main() {
  int *x = malloc(sizeof(int));
  int t = _;
  *x = t;
  assert(P(x));

  int *y;
  assume(P(y));

  assert(*y == t);
}
