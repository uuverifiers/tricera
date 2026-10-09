int f(long long x) {
  return x;
}

void main() {
  long long big = 4294967296;
  long long y = f(big);
  assert(y != 0);
}
