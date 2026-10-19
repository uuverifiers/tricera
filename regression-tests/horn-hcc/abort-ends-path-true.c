extern int __VERIFIER_nondet_int(void);
extern void abort(void);

void assume_abort_if_not(int cond) {
  if (!cond) abort();
}

int main() {
  int x = __VERIFIER_nondet_int();
  assume_abort_if_not(x > 0);
  assert(x > 0);
  return 0;
}
