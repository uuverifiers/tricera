int nondet();

void main() {
  int *a = malloc(sizeof(int));
  free(a);
  int *b = a; // safe
}
