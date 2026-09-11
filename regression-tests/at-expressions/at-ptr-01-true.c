#include <stdlib.h>

int *p;

void main() {
  p = malloc(sizeof(int));
  *p = 3;
  L: ;
  p = 0;
  assert(*$at("L", (int *) p) == 3);
}
