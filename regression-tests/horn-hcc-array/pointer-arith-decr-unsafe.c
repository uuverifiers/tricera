int a[];

void main() {
  int n = 3;
  a = calloc(sizeof(int)*n);
  int *p = a;
  p--;
  assert(*p == 0);
  free(a);
}
