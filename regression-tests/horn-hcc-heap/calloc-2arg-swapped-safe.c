void main() {
  int *x = calloc(sizeof(int), 1);
  assert(*x == 0);
}
