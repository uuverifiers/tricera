int g = 0;

int not_in_thread(int x) {
  return x + 100;
}

int helper(int x) {
  assert(x == 3);
  return x;
}

thread T {
  g++;
  g++;
  helper(g);
}
