int a[];

void main() {
  int n = 2;
  a = calloc(sizeof(int)*n);
  int *p = &(a[1]);
  for(int i = 0; i < n; ++i) {
    if(*p != 0) {
      reach_error();
    }
    // Above the read *p is unsafe (valid-deref),
    // reach_error will also be hit (unreach-call), that location might not contain 0.
    p = p+1;
  }
  free(a);
}
