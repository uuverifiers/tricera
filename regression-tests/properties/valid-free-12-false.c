#include <stdlib.h>

void main() {
  int *a = malloc(sizeof(int));
  int addrA = (int) a; // safe in ILP32 - violates MISRA-C 11.4 and not supported by TriCera
  // TriCera is expected to reject above line (report unknown for this benchmark). 
  free(a); // a is freed, addrA still holds prev. addr value
  int *b = malloc(sizeof(int));
  int addrB = (int) b;
  if (addrA == addrB) { // this is possible, b might get alloced the freed address
    free(b);
  }
  free(b); // potential double free
}
