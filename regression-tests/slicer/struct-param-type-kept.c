struct S {
  int x;
};

int dead_global = 99;

int is_null(struct S *p) {
  if (p == 0) {
    return 1;
  } else {
    return 0;
  }
}

int main(void) {
  int r = is_null(0);
  assert(r == 1);
  return 0;
}
