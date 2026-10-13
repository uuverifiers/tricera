struct S { _Bool f; };

int main() {
  int v = 5;
  struct S s = { v };
  s.f = 2;
  assert(s.f != 1);
  return 0;
}
