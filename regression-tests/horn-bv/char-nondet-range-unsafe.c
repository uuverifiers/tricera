char __VERIFIER_nondet_char(void);
unsigned char __VERIFIER_nondet_uchar(void);

int main() {
  char c = __VERIFIER_nondet_char();
  unsigned char u = __VERIFIER_nondet_uchar();
  assert(c < -128 || c > 127);
  return 0;
}
