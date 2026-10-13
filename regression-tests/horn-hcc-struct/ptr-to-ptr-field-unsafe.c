// a struct field declared with two pointer levels

#include <stdlib.h>

struct S { int **pp; };

int main() {
  struct S s = {0};
  s.pp = malloc(sizeof(int *));
  *s.pp = malloc(sizeof(int));
  **s.pp = 3;
  int *p = *s.pp;
  assert(*p != 3);
  return 0;
}
