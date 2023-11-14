#include <assert.h>

void main() {
  int a[_]; // [_] denotes that a is a mathematical array that is allocated everywhere
  int n = 5;
  int i = 0;
  for(i = 0; i < n; ++i) {
    a[i] = i;
  }
  
  assert(\max(a, 0, 5) == n);
}
