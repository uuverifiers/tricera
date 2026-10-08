struct S { int x; };

void main() {
  struct S s;
  s.x = 1;
  int *p = (int *)&s;
  assert(*p == 1);
}
