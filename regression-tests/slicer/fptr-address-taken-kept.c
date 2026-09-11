void handler(void) {
  int z = 1;
  assert(z == 1);
}

void reallyDead(void) {
  int w = 2;
  assert(w == 2);
}

int main(void) {
  void (*fp)(void) = handler;
  int y = 4;
  assert(y == 4);
  return 0;
}
