#include <stdlib.h>

void freePtr(int *q) {
  free(q);
}

void main() {
  int *p = malloc(sizeof(int)*10);
  freePtr(p);
}
