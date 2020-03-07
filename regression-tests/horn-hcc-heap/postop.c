void main() {
  int *x = calloc(sizeof(int));
  assert((*x)++ == 0);
  assert((*x)-- == 1);
  assert(*x == 0);
}

