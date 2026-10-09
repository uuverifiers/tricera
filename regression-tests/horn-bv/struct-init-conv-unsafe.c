struct S { int x; };

void main() {
  long long big = 4294967296;
  struct S s = { big };
  long long y = s.x;
  assert(y != 0);
}
