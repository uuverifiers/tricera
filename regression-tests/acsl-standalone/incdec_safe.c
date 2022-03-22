/*@
  ensures \result == n+1;
*/
int inc(int n) {
  return n+1;
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
