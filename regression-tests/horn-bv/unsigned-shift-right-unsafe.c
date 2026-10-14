int main() {
  unsigned int x = 0x80000000u;
  assert((x >> 1) != 0x40000000u);
  x >>= 1;
  assert(x == 0x40000000u);
  unsigned long y = (unsigned long)-1;
  assert((y >> 1) == (unsigned long)-1 / 2);
  return 0;
}
