#include <stdlib.h>

int main() {
  int *p = malloc(sizeof(int));
  *p = 5;
  /*@ requires \valid(p);
      ensures  *p == \old(*p) + 1;
  */
  { *p = *p + 2; }
  return 0;
}
