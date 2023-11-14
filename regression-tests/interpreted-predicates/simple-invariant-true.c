/*$
SimpleInvariant(int x) {
  x == 42
}
$*/

void main() {
  int x;
  assume(SimpleInvariant(x));
  assert(x == 42);
}
