#include <stdlib.h>
int main() {
  int x = 0;
  int *p = malloc(sizeof(int) * 2);
  p = 0;
  if (p) x = 1;
  assert(x == 1);
  return 0;
}
