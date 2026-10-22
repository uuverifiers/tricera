extern int __VERIFIER_nondet_int(void);
int len;
void main() {
  len = __VERIFIER_nondet_int();
  assume(len >= 0);
  int a[len + 1];
  a[0] = 1;
  assert(a[0] == 1);
}
