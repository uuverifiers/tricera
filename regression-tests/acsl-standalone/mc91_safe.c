/*@
  ensures n <= 100 ==> \result == 91;
  ensures n > 100 ==> \result == n-10;
*/
int foo(int n) {
  if (n > 100) {
    return n - 10;
  } else {
    return foo(foo(n + 11));
  }
}
