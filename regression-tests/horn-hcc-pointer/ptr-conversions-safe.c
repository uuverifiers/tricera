struct S { int f; };

int first(int *p) { return p[0]; }

void main() {
  int x = 1;
  void *v = &x;
  int *p = v;
  int **pp = &p;
  struct S s;
  s.f = 2;
  int *q = &s.f;
  int a[2] = {3, 4};
  assert(**pp == 1 && *q == 2 && first(a) == 3);
}
