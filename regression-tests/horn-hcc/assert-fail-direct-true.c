extern void __assert_fail(const char *, const char *, unsigned int, const char *);
extern int __VERIFIER_nondet_int(void);

int main() {
  int x = __VERIFIER_nondet_int();
  if (x > 10) x = 10;
  if (!(x <= 10))
    __assert_fail("x <= 10", "assert-fail-direct-true.c", 7, "main");
  return 0;
}
