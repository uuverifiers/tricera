enum E { A, B };
enum F { N = -1, P };

void set_uint(unsigned *p) { *p = 1; }
void set_int(int *p) { *p = 0; }

int main() {
  enum E e = A;
  set_uint(&e);
  enum F f = N;
  set_int(&f);
  assert(e == B);
  assert(f == P);
  return 0;
}
