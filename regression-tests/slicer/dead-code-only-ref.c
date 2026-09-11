// 'only_in_dead' is referenced only by the unreachable 'dead', so both are dropped
int only_in_dead = 7;

static int dead(void) {
  return only_in_dead + 1;
}

int main(void) {
  int x = 2;
  assert(x == 2);
  return 0;
}
