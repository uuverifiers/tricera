struct S {
  int x;
};

int dead_global = 99;

int main(void) {
  void *vp = malloc(sizeof(int));
  ((struct S *)vp)->x = 5;
  assert(((struct S *)vp)->x == 5);
  return 0;
}
