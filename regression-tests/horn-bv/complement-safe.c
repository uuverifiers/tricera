int main() {
  int s = 5;
  assert(~s == -6);
  unsigned int u = 0x0Fu;
  assert(~u == 0xFFFFFFF0u);
  unsigned char c = 0;
  assert(~c == -1);
  return 0;
}
