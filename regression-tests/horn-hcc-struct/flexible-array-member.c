struct F { int k; int a[]; };

int main() {
  struct F f = {1};
  assert(f.k == 1);
  return 0;
}
