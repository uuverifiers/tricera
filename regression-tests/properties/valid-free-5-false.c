#include <stdlib.h>

void main() {
  int x;
  int *y = &x;
  free(y); // not OK, because y is a stack pointer.
}
