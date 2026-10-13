enum E { A, B };

int main() {
  long long big = 4294967296;
  long long y1 = (enum E) big;
  enum E c = A;
  c += big;
  long long y2 = c;
  assert(y1 != 0);
  return 0;
}
