int main() {
  int x = 42;
  if(x == 42) {
    abort();
  } else {
    exit(0);
  }
  assert(0); // unreachable
  return 0;
}
