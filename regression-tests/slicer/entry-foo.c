// run with -m:foo; main is unreachable from foo and is dropped
int foo(void) {
  int x = 1;
  assert(x == 1);
  return 0;
}

int main(void) {
  int y = 99;
  assert(y == 100);
  return 0;
}
