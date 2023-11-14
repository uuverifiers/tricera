#include <assert.h>

void main() {
  int a[_]; // [_] denotes that a is a mathematical array that is allocated everywhere
  int n = 3;
  int i = 0;
  for(i = 0; i < n; ++i) {
    a[i] = i;
  }
  
  assert(\sum(a, 0, 3) == 3);
}
