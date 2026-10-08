#include <stdlib.h>

struct A { int tag_A; };
struct B { int tag_B; };

int get(struct A *a) { return a->tag_A; }

void main() {
  struct B *b = malloc(sizeof(struct B));
  b->tag_B = 2;
  assert(get(b) == 2);
}
