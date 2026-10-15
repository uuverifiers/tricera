#include <stdlib.h>

int f(int x[]) { return x[0]; }

int main() {
  int *p = malloc(sizeof(int));
  *p = 0;
  f(p);
  return 0;
}
