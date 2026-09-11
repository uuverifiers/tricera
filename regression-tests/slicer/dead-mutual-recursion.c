int pong(int n);

int ping(int n) {
  if (n <= 0) return 0;
  return pong(n - 1);
}

int pong(int n) {
  if (n <= 0) return 1;
  return ping(n - 1);
}

int main(void) {
  int x = 3;
  assert(x == 3);
  return 0;
}
