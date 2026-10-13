int main() {
  _Bool b = 1;
  assert(b + 1 == 2);
  assert(b + b == 2);
  b++;
  assert(b == 1);
  return 0;
}
