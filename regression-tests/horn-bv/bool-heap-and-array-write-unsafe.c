#include <stdlib.h>

int main() {
  int v = 2;
  _Bool *p = malloc(sizeof(_Bool));
  _Bool a[2];
  a[1] = v;
  if (p) {
    *p = v;
    assert(*p != 1);
  }
  return 0;
}
