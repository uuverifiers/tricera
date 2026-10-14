int main() {
  unsigned int x = 0x80000000u;
  long long n = 1;
  assert((x << n) != 0);
  int s = -8;
  unsigned int m = 1;
  assert((s >> m) == -4);
  return 0;
}
