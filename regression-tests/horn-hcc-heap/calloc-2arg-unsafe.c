void main() {
  int *x = calloc(1, sizeof(int));
  assert(*x == 42);
}
