#include <stdlib.h>

int main() {
  int *p = malloc(sizeof(int));
  *p = 0;
  /*@ requires \valid(p) && *p == 0;
      ensures  *p >= 1 && *p <= 10;
      assigns  *p;
  */
  { *p = 5; }
  //@ assert *p == 5;
  return 0;
}
