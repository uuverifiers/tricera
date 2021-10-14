int nondet();

void main() {
  int *a = malloc(sizeof(int));
  free(a);
  int *b = malloc(sizeof(int));
  assert(a != b); // known limitation:
                  // unsafe, but current implementation returns safe...
}
