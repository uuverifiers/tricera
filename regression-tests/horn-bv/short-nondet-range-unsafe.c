short __VERIFIER_nondet_short(void);
unsigned short __VERIFIER_nondet_ushort(void);

int main() {
  short s = __VERIFIER_nondet_short();
  unsigned short u = __VERIFIER_nondet_ushort();
  assert(s < -32768 || s > 32767);
  return 0;
}
