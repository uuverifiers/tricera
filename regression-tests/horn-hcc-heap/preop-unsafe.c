void main() {
  int *x = calloc(sizeof(int));
  assert(++(*x) == 0);
}
