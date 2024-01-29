#include <stdlib.h>

void foo() {
  int *x = alloca(sizeof(int));
  free(x);
}

void main() {
  foo();
}
