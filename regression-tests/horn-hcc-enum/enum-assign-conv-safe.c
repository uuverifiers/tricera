enum E { A, B };

void main() {
  long long big = 4294967296;
  enum E e = B;
  e = big;
  switch (e) {
    case A: break;
    default: assert(0);
  }

  e = -1;
  assert(e > 0);
}
