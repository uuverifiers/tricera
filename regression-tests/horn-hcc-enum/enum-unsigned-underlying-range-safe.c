unsigned __VERIFIER_nondet_uint(void);

enum E { A, B };

int main() {
  enum E u = __VERIFIER_nondet_uint();
  long long y = u;
  enum E m = -1;
  assert(y >= 0 && y < 4294967296);
  assert(m > 0);
  return 0;
}
