int main() {
  int *x = malloc(sizeof *x);
  free(x);
  return 0;
}
