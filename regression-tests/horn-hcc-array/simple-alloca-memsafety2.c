int foo() {
  int a[];
  a = alloca(sizeof(int)*42);
  a[0] = 3;
  return a[0];
}

void main() {
  assert(foo() == 3);
}
