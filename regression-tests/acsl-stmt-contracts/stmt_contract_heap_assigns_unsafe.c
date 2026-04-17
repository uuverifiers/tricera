#include <stdlib.h>

int main() {
  int *p = malloc(sizeof(int));
  int *q = malloc(sizeof(int));
  *p = 0;
  *q = 100;
  /*@ requires \valid(p) && \valid(q);
      ensures  *p == \old(*p) + 1;
      assigns  *p;
  */
  { (*p)++; (*q)++; }
  return 0;
}
