int a[4];

/*@contract@*/
void increment(int x[], unsigned n) {
  x[n] += 1;
}

int main() {
  increment(a + 1, 1);
  assert(a[2] == $at("Old", (int)(a[2])) + 1);
  return 0;
}
