int main() {
  unsigned char c = 255;
  c = c + 1;
  assert(c == 0);
  c--;
  assert(c == 255);
  return 0;
}
