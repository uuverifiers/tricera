#include <stdlib.h>

int main() {
  unsigned *p = malloc(sizeof(unsigned));
  if (p) {
    *p = -1;
    assert(*p > 5);
  }
  return 0;
}
