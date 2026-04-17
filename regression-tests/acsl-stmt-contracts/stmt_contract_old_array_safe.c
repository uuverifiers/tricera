#include <stdlib.h>

int main() {
  int *a = (int*) malloc(3 * sizeof(int));
  a[0] = 10; a[1] = 20; a[2] = 30;
  /*@ ensures a[1] == \old(a[1]) + 1; */
  { a[1] = a[1] + 1; }
  //@ assert a[1] == 21;
  return 0;
}
