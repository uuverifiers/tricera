struct S {
  int *f;
};

void alloc(struct S *ps) {
  ps->f = (int *)malloc(sizeof(int));
  *(ps->f) = 42;
}

int main() {
  struct S s;
  alloc(&s);
  free(s.f);
  return 0;
}
