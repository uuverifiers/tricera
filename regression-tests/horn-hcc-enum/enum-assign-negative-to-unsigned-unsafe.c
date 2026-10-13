enum E { A, B };

int main() {
  enum E e = A;
  e = -1;
  assert(e <= 0);
  return 0;
}
