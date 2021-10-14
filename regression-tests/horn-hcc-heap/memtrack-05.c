void foo(int **x) {
  *x = malloc(sizeof(int));
}

int main() {
  int *x;
  foo(&x);
  return 0; // unsafe
}
