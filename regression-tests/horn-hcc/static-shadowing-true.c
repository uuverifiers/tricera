#include <stdio.h>

int x;

int foo() {
  static int x;
  x = x + 1; // This should increment the local x
  return x;
}

int main() {
  int y;
  foo(); // foo::x = 1
  y = foo(); // y = foo::x == 2
  assert(y == 2);
  assert(x == 0); // global x should be unchanged
}
