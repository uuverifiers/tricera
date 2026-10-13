#include <stdlib.h>

int main() {
  int x = 0;
  int *nullPtr = 0;
  int *heapPtr = malloc(sizeof(int));
  if (heapPtr) {
    assert((_Bool)heapPtr != 1);
  }
  return 0;
}
