/*$ P(int x) $*/

void main() {
  assert(P(42));
  int x;
  assume(P(x));
  assert(x == 43);
}
