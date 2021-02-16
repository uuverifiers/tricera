int nondet();

void main() {
  int *a = malloc(sizeof(int));
  if(nondet())
    free(a);
  *a = 42; // unsafe - possible use after free
}
