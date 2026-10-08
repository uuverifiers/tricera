enum E { A, B };
enum F { N = -1, P };

struct S { enum E a[2]; };

void set_uint(unsigned *p) { *p = 1; }
void set_int(int *p) { *p = 0; }

void main(void)
{
  long long big = 4294967296;

  long long y1 = (enum E) big;
  assert(y1 == 0);

  enum E c = A;
  c += big;
  long long y2 = c;
  assert(y2 == 0);

  enum E s = big;
  switch (s) {
    case A: break;
    default: assert(0);
  }

  enum E u;
  long long y3 = u;
  assert(y3 >= 0 && y3 < 4294967296);

  struct S st;
  st.a[1] = B;
  assert(st.a[1] == B);

  enum E m = -1;
  assert(m > 0);

  enum E e = A;
  set_uint(&e);
  assert(e == B);

  enum F f = N;
  set_int(&f);
  assert(f == P);
}
