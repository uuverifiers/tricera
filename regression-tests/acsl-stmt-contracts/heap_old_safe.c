#include <stdlib.h>

int main() {
  int *p = malloc(sizeof(int));
  *p = 5;
  /*@ requires \valid(p);
      ensures  *p == \old(*p) + 1;
  */
  { (*p)++; }
  //@ assert *p == 6;
  return 0;
}
