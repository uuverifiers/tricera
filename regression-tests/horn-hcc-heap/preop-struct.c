struct S {
  int x;
} *s;

void main() {
  s = calloc(sizeof(struct S));
  assert(++(s->x) == 1);
  assert(--(s->x) == 0);
}

