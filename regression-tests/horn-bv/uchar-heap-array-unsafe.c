#include <stdlib.h>

int main() {
  unsigned char *a = malloc(2 * sizeof(unsigned char));
  a[0] = 7;
  a[1] = -2;
  assert(a[1] != 254);
  return 0;
}
