#include <stdlib.h>

int main() {
  int x = 0;
  int *nullPtr = 0;
  int *heapPtr = malloc(sizeof(int));
  assert((_Bool)nullPtr == 0);
  assert((_Bool)&x == 1);
  if (heapPtr) {
    assert((_Bool)heapPtr == 1);
  }
  return 0;
}
