#include <stdlib.h>
int main() {
  void *v = malloc(sizeof(int));
  int *p = (int *) v;
  *p = 3;
  void *w = (void *) p;
  int *q = (int *) w;
  assert(*q == 4);
  return 0;
}
