int never_called(int x) {
  return x - 1;
}

int c(int x) {
  assert(x == 11);
  return x;
}

int b(int x) {
  return c(x + 5);
}

int a(int x) {
  return b(x + 5);
}

int main(void) {
  int r = a(0);
  return r;
}
