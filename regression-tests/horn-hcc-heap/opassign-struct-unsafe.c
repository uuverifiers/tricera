struct S {
  int x;
} *s;

void main() {
  s = calloc(sizeof(struct S));
  s->x += 42;
  s->x *= 2;
  s->x /= 4;
  assert(s->x == 42);
}
