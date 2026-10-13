int first(int *p) { return p[0]; }

int main() {
  int a[2] = {3, 4};
  assert(first(a) == 3);
  return 0;
}
