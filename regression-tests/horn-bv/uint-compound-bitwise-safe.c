int main() {
  unsigned int x = 0xF0u;
  x |= 0x0F;
  x &= 0x3C;
  assert(x == 0x3Cu);
  unsigned long long y = 1;
  y <<= 40;
  y >>= 38;
  assert(y == 4);
  return 0;
}
