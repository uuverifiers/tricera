void foo(int **x) {
  *x = malloc(sizeof(int));
}

int main() {
  int *x;
  foo(&x);
  free(x);
  return 0; // safe
}
