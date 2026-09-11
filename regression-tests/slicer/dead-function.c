int reachable_fn(int x) {
  return x + 1;
}

int dead_fn(int x) {
  return x - 1;
}

int main(void) {
  int r = reachable_fn(10);
  assert(r == 11);
  return 0;
}
