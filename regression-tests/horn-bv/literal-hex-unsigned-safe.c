int main() {
  assert(-1 / 0xFFFFFFFF == 1);
  assert(-1 / 4294967295 == 0);
  return 0;
}
