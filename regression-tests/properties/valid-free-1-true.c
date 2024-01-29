#include <stdlib.h>

void main() {
  int *x = malloc(sizeof *x);
  free(x);
}
