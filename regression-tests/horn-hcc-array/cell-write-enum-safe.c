#include <stdlib.h>

enum E { A, B };

int main() {
  enum E e[1];
  e[0] = B;
  enum E *q = malloc(sizeof(enum E));
  assert(e[0] == B);
  if (q) {
    *q = A;
    assert(*q == A);
  }
  return 0;
}
