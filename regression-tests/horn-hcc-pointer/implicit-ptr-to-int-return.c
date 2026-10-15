#include <stdlib.h>

int f(int *p) { return p; }

int main() {
  int *a = malloc(sizeof(int));
  int x = f(a);
  return 0;
}
