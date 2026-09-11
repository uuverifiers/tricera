// only 'b' is used, but the whole 'a, b' declaration is kept
int a, b;
int dead;

int main(void) {
  b = 5;
  assert(b == 5);
  return 0;
}
