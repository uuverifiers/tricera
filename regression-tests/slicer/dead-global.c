int g_used = 5;
int g_dead = 7;

int main(void) {
  int x = g_used + 1;
  assert(x == 6);
  return 0;
}
