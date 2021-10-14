#include <stdlib.h>
#include <assert.h>

extern int nondet();

int a[];

void main() {
  int n = nondet();
  assume(n > 0);
  a = malloc(sizeof(int)*n);
  a[n] = 42;
}
