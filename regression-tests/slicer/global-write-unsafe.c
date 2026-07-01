int result = 0;
int unused_global = 7;

void compute(int a, int b) {
  result = a + b;
}

int main(void) {
  compute(3, 4);
  assert(result == 8);
  return 0;
}
