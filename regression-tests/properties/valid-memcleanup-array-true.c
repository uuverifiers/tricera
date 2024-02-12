#include <stdlib.h>

int* allocArray(int n) {
  return malloc(sizeof(int)*n);
}

void freePtr(int *q) {
  free(q);
}

void main() {
  int p[] = allocArray(10); 
  /* Note that int * p = ... does not work, and will be unsafe,
     because tricera currently cannot recognize p as an array pointer,
     and as a result incorrectly treats AddrRange as Addr sort.
  */                           
  freePtr(p);
}
