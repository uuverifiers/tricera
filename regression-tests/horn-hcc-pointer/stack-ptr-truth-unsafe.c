int main() {
  int x;
  int *p = &x;
  int y = 0;
  if (p) y = 1;
  assert(y == 0);
  return 0;
}
