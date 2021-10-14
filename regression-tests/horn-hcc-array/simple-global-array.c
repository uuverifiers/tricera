int a[10];

void main() {
  assert(a[0] == 0);
  a[1] = 40;
  assert(a[1] == 40);
  a[2] = 2;
  assert(a[1] + a[2] == 42);
}
