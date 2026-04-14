void main() {
  int *x = calloc(sizeof(int));
  *x += 42;
  *x *= 2;
  assert(*x == 42);
}
