/*@
  requires \true;
  ensures \result == 1;
  throws { int, char } a == 0;
  throws { char, long } b < 0;
*/
int foo(int a, int b) {
  if (a == 0) {
    if (b > 0) {
      throw 'a';
    }
    throw 1;
  }
  if (b < -1) {
    throw 2l;
  }
  return 1;
}


int main() {
  int x;
  try {
    x = foo(0, -1);
  } catch (...) {}
  return 0;
}