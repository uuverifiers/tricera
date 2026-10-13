enum E { A, B };

int main() {
  long long big = 4294967296;
  enum E e = B;
  e = big;
  switch (e) {
    case A: break;
    default: assert(0);
  }
  return 0;
}
