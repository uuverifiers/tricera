#include <stdlib.h>

int main() {
  int *nullPtr = 0;
  int *heapPtr = malloc(sizeof(int));
  _Bool c = 1;
  c = nullPtr;
  assert(c == 0);
  if (heapPtr) {
    c = heapPtr;
    assert(c == 1);
  }
  return 0;
}
