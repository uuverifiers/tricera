struct S { int f; };

int main() {
  struct S s = { 2 };
  int *q = &s.f;
  assert(*q != 2);
  return 0;
}
