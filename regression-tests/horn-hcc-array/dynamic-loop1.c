#include <stdlib.h>
#include <assert.h>

extern int nondet();

int a[];

void main() {
  //  int n = nondet(); // cannot verify
  int n = 2;
  a = malloc(sizeof(int)*n);

  for (int i = 0; i < n; ++i) {
    a[i] = 3;
  }
  
  int sum = 0;
  for (int i = 0; i < n; ++i) {
    sum += a[i];
    assert(a[i] == 3);
  }
  
  assert(sum == n*3);

  free(a);
}
