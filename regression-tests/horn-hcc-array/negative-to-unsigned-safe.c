#include <stdlib.h>

int main() {
  unsigned a[2];
  a[0] = -1;
  assert(a[0] > 5);

  unsigned *p = malloc(sizeof(unsigned));
  *p = -1;
  assert(*p > 5);

  unsigned u = -1;
  assert(u == 4294967295);

  int m = -1;
  unsigned v = m;
  assert(v > 5);
  return 0;
}
