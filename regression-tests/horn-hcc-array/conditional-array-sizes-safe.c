extern int __VERIFIER_nondet_int(void);
int a[2], b[3];
int main() {
  int c = __VERIFIER_nondet_int();
  int *p = c ? a : b;
  p[1] = 5;
  assert(c ? a[1] == 5 : b[1] == 5);
  return 0;
}
