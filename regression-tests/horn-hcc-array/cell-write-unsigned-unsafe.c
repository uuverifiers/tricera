#include <stdlib.h>

int main() {
  unsigned a[1];
  a[0] = 5;
  unsigned *p = malloc(sizeof(unsigned));
  if (p) {
    *p = 6;
    assert(*p != 6);
  }
  return 0;
}
