int main() {
  unsigned char c = 0;
  c--;
  assert(c == 255);
  unsigned short s = 3;
  s -= 5;
  assert(s == 65534);
  return 0;
}
