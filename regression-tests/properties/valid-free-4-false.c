#include <stdlib.h>

void main() {
  int *x;
  free(x); // not OK, because x is uninitialized and not null.
}
