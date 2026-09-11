#include <stdlib.h>

int *q;

void f(int *p) {
  *p = 3;
  p = 0;
  assert(*$at("Old", (int *) p) == 4);
}

void main() {
  q = malloc(sizeof(int));
  f(q);
}
