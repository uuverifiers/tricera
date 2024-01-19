#include <stdlib.h>

void foo() {
  int *x = alloca(sizeof(int)*3);
  free(x);
}

void main() {
  foo();
}
