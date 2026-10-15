int main() {
  unsigned x = 0xFFFFFFFFu;
  assert(x == -1);
  assert(-1 == x);
  return 0;
}
