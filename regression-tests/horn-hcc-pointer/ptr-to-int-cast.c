#include <stdlib.h>

void main() {
  int *a = malloc(sizeof(int));
  int addrA = (int) a; // safe in ILP32 - violates MISRA-C 11.4 and not supported by TriCera
}
