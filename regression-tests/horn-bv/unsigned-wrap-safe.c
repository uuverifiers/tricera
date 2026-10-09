struct S { unsigned f; };

void main() {
  unsigned u = 0;
  u = -1;
  assert(u > 0);

  struct S s;
  s.f = -1;
  assert(s.f > 0);
}
