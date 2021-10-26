#include <assert.h>
#include <stdlib.h>

int foo (int a[]) {
  a[0] = 0;
  return a[0];
}

void main() {
  int a[] = calloc(sizeof(int) * 1); // not standard C, simplified
  int res = foo(a);
  assert(res == 0);
}
