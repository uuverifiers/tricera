extern int __VERIFIER_nondet_int(void);
int main() {
  int c = __VERIFIER_nondet_int();
  int positive = (c ? -1 : 0u) > 0;
  if (c) assert(positive);
  return 0;
}
