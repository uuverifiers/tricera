/*$
SimpleInvariant(int x) {
  x == 3
}
$*/

void main() {
  int x;
  assume(SimpleInvariant(x));
  assert(x == 42);
}
