struct S { int a[2], k; int m, b[2]; };

int main() {
  struct S s = {{1, 2}, 3, 4, {5, 6}};
  assert(s.k != 3 || s.b[1] != 6);
  return 0;
}
