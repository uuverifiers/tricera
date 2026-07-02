static int unused_static(int x) {
  return x - 7;
}

static int s_fn(int x) {
  assert(x == 5);
  return x * 2;
}

inline int i_fn(int x) {
  assert(x == 11);
  return x + 1;
}

int main(void) {
  int a = s_fn(5);
  int b = i_fn(a);
  return a + b;
}
