#include <stdlib.h>

enum E { A, B };

void main() {
  unsigned a[2];
  a[0] = 5;
  assert(a[0] == 5);

  unsigned *p = malloc(sizeof(unsigned));
  *p = 5;
  assert(*p == 5);

  enum E e[2];
  e[0] = B;
  assert(e[0] == B);

  enum E *q = malloc(sizeof(enum E));
  *q = B;
  assert(*q == B);
}
