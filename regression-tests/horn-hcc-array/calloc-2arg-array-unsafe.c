int a[];

void main() {
  int n = 2;
  a = calloc(n, sizeof(int));
  int *p = a;
  for(int i = 0; i <= n; ++i) {
    assert(*p == 0);
    p = p+1;
  }
  free(a);
}
