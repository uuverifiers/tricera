#include <stdlib.h>

void* allocArray(int n) {
  return malloc(sizeof(int)*n);
}

void main() {
  int p[] = (int*) allocArray(10);
}
