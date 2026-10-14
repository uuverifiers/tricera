int main() {
  unsigned char c = 200;
  c >>= 1;
  c |= 0x101;
  assert(c != 101);
  unsigned short s = 0x8001;
  s <<= 1;
  assert(s == 2);
  return 0;
}
