void f(int e) {
  long long y = e;
  assert(y != 0);
}

void main() {
  long long big = 4294967296;
  f(big);
}
