int main() {
  int i = 40000;
  short s = 0;
  s = i;
  assert(s == -25536);
  unsigned short u = 0;
  u = -i;
  assert(u == 25536);
  return 0;
}
