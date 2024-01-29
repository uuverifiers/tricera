int a[];

void main() {
  int n = 2;
  a = calloc(sizeof(int)*n);
  int *p = &(a[0]);
  for(int i = 0; i < n; ++i) {
    assert(*p == 0);
    p = p+1;
  }
  free(a);
}
