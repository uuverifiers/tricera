#include <stdlib.h>

int main() {
  int x = 0;
  int *nullPtr = 0;
  int *heapPtr = malloc(sizeof(int));
  _Bool fromNull = nullPtr;
  _Bool fromStack = &x;
  if (heapPtr) {
    _Bool fromHeap = heapPtr;
    assert(fromHeap != 1);
  }
  return 0;
}
