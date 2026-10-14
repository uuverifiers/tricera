int main() {
  unsigned char a = 200, b = 100;
  int s = a + b;
  assert(s == 300);
  assert(b - a == -100);
  return 0;
}
