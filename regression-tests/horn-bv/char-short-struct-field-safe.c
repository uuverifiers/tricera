struct S { unsigned char c; unsigned short s; int i; };

int main() {
  struct S x = { -1, 5, 7 };
  x.s = -2;
  assert(x.c == 255);
  assert(x.s == 65534);
  return 0;
}
