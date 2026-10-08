enum E { A, B };

void main() {
  enum E e = B;
  int *p = &e;
  assert(*p == 1);
}
