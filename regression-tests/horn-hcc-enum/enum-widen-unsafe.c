enum E { A, B };

int main() {
  long long big = 4294967296;
  enum E e = big;
  long long y = e;
  assert(y != 0);
  return 0;
}
