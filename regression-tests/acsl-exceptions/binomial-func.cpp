struct DomainErr {};
struct ArgumentErr {};

/*@
  ensures \result >= 1;
  ensures (k == 0 || k == n) ==> \result == 1;
  ensures k == 1 ==> \result == n;
  throws { struct DomainErr } n < 0 || k < 0;
  throws { struct ArgumentErr } k > n;
*/
int binomial(int n, int k) {
  struct DomainErr domain_err;
  struct ArgumentErr arg_err;
  int r1; int r2;

  if (n < 0 || k < 0) throw domain_err;
  if (k > n) throw arg_err;
  if (k == 0 || k == n) return 1;

  r1 = binomial(n - 1, k - 1);
  r2 = binomial(n - 1, k);
  return r1 + r2;
}

int main() {
  int x; x = binomial(5, 3);
  return 0;
}