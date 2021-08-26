#include <stdlib.h>
#include <assert.h>

extern int nondet();

int a[];

void main() {
  int n = 1;
  a = malloc(sizeof(int)*n);

  for (int i = 0; i <= n; ++i) {
    a[i] = 3;
  }
  free(a);
}
