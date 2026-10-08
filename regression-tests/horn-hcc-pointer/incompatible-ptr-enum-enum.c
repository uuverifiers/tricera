enum E { A, B };
enum E2 { X, Y };

void main() {
  enum E e = B;
  enum E2 *p = &e;
  assert(*p == Y);
}
