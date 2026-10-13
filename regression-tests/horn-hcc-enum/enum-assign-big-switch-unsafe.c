enum E { A, B };

int main() {
  long long big = 4294967296;
  enum E e = B;
  e = big;
  switch (e) {
    case A: assert(0);
    default: break;
  }
  return 0;
}
