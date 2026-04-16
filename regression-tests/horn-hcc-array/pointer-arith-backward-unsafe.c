int a[];

void main() {
  int n = 3;
  a = calloc(sizeof(int)*n);
  int *p = a;
  p = p - 1;
  assert(*p == 0);
  free(a);
}
