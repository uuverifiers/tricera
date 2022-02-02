/*@
  ensures \result == n+2;
*/
int inc(int n) {
  return n+2;
}

/*@
  ensures \result == n-1;
*/
int dec(int n) {
  return n-1;
}

/*@
  ensures \result == n;
*/
int foo(int n) {
  return inc(dec(n));
}
