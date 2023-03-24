/*$
P(int x, int i, int n) {
  x == i*n && i <= n //0 <= i not needed
}
$*/

void main() {
  int n = _;
  assume(n > 0);
  int x = 0;
  int i = 0;
  assert(P(x, i, n));
  while (i < n) {
    assume(P(x, i, n)); // does not work without this assumption
    x += n;
    i++;
    assert(P(x, i, n));
  }
  assume(P(x, i, n));

  
  assert(x != n*n);
}
