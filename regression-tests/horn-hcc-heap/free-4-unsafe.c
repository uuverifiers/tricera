int nondet();

void main() {
  int *a = malloc(sizeof(int));
  free(a);
  int *b = a;
  *b = 42;
}
