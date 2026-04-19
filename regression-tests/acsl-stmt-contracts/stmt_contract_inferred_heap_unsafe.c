#include <stdlib.h>

int main() {
  int *p = malloc(sizeof(int));
  *p = 5;
  /*@ contract @*/
  { (*p)++; }
  //@ assert *p == 10;
  return 0;
}
