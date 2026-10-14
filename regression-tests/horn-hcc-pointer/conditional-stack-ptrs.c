extern int __VERIFIER_nondet_int(void);
int main() {
  int x = 0, y = 0;
  int c = __VERIFIER_nondet_int();
  int *p = c ? &x : &y;
  *p = 1;
  assert(c ? x == 1 : y == 1);
  return 0;
}
