enum E { A, B };

void main(void)
{
  long long big = 4294967296;
  enum E e = big;
  long long y = e;
  assert(y != 0);
}
