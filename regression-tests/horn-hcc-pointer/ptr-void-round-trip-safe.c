int main() {
  int x = 1;
  void *v = &x;
  int *p = v;
  assert(*p == 1);
  return 0;
}
