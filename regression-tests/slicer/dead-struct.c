struct Used { int a; };
struct Dead { int b; };

int main(void) {
  struct Used u;
  u.a = 9;
  assert(u.a == 9);
  return 0;
}
