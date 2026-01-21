/*$
P(int x, int i, int n) {
  x == i*n && i <= n && 0 <= i
}
$*/

void main() {
  int n = _;
  assume(n > 0);
  int x = 0;
  int i = 0;
  assert(P(x, i, n));

  int b = _;
  if(b) {
    x = _; i = _; n = _;
    assume(i < n);
    assume(P(x, i, n));
    x += n;
    i++;
    assert(P(x, i, n));
    assume(0);
  } else {
    x = _; i = _; n = _;
    assume(i >= n);
    assume(P(x, i, n));
  }

  // while (i < n) {
  //   x = _; i = _; n = _;
  //   assume(P(x, i, n));
  //   x += n;
  //   i++;
  //   assert(P(x, i, n));
  // }
  // x = _; i = _; n = _;
  // assume(P(x, i, n));

  
  assert(x == n*n);
}
