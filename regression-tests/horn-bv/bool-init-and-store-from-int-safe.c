int main() {
  int v = 5;
  int w = 2;
  _Bool b = v;
  assert(b == 1);
  _Bool c = 0;
  c = w;
  assert(c == 1);
  return 0;
}
