#include <stdlib.h>
int main() {
  int *a = malloc(2 * sizeof(int));
  _Bool b = a;
  assert(b);
  return 0;
}
