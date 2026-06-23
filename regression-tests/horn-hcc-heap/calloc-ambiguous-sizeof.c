void main() {
  int *x = calloc(sizeof(int), sizeof(char));
  assert(*x == 0);
}
