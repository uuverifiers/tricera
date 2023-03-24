/*$ P(int x) $*/

void main() {
  assert(P(42)); // push

  int x;
  assume(P(x));  // pull

  assert(x == 42);
}
