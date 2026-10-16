#include <stdlib.h>
int main() {
  int *p = malloc(sizeof(int) * 2);
  p = 0;
  assert(p != 0);
  return 0;
}
