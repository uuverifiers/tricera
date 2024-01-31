#include <stdlib.h>

struct S { int data; };

void access(int *x){
  *x;
}

void main() {
  struct S *s = malloc(sizeof(struct S));
  access(&(s->data));
}