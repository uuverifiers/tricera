#include <stdlib.h>

void main() {
  int *x = 0;
  free(x); // OK because x is null pointer.
}
