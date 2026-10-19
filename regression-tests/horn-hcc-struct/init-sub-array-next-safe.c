struct S { int a[3]; int k; };

int main() {
  struct S s = {{1, 2}, 5};
  assert(s.k == 5);
  return 0;
}
