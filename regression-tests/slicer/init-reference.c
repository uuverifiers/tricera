// 'base' is referenced only in the initializer of the live global 'derived'
int base = 10;
int derived = base;
int unused = 99;

int main(void) {
  assert(derived == 10);
  return 0;
}
