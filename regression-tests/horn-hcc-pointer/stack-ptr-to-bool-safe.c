int __VERIFIER_nondet_int(void);

int main() {
  int x = __VERIFIER_nondet_int();
  _Bool c = &x;
  _Bool d;
  d = &x;
  assert(c == 1);
  assert(d == 1);
  return 0;
}
