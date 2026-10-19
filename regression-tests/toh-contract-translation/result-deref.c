#include <stdlib.h>

/*@contract@*/
int *mk() {
  int *p = malloc(sizeof(int));
  *p = 3;
  return p;
}

int main() {
  int *q = mk();
  assert(*q == 3);
  return 0;
}
