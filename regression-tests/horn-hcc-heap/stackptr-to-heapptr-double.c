#include <stdlib.h>

void main () {
  int *x1, *x2;
  int y = 42;
  x1 = &y;
  x2 = &y;
  assert(x1 == x2);
}