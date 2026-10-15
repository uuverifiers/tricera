int __VERIFIER_nondet_int(void);

int main() {
  int a[2];
  a[0] = __VERIFIER_nondet_int();
  a[1] = 5;
  *a = 0;
  assert(a[0] == 0);
  assert(a[1] == 5);
  return 0;
}
