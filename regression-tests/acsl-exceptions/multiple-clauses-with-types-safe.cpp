/*@
  requires \true;
  assigns \nothing;
  ensures \result == 1;
  throws { int, long } n < 0;
  throws { char } n == 10;
*/
int foo(int n) {
  if (n < -10) throw 0;
  if (n < 0) throw 1l;
  if (n == 10) throw 'a';
  return 1;
}

int main() {
  int x;
  try {
    x = foo(0);
  } catch (...) {}
  return 0;
}
