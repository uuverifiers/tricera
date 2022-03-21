#include <assert.h>
#include <stdlib.h>

typedef struct S {
  int data[4];
} S;

int foo (int a[]) {
  a[0] = 0;
  return a[0];
}

void main() {
  S s;
  for(int i = 0; i < 4; ++i) {
    s.data[i] = i;
  }
  for(int i = 0; i < 4; ++i) {
    assert(s.data[i] != i);
  }
}
