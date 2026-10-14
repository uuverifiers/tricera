int main() {
  int n = 0;
  char *c = (char *)&n;
  assert(*c == 0);
  return 0;
}
