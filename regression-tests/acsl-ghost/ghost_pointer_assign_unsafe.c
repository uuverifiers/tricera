#include <stdlib.h>

int main() {
  /*@ ghost int *p = (int*)malloc(sizeof(int));
             *p = 42;
  */
  //@ assert *p == 99;
  return 0;
}
