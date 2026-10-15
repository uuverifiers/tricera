#include <stdlib.h>

int f(int v) { return v; }

int main() {
  int *a = malloc(sizeof(int));
  int x = f(a);
  return 0;
}
