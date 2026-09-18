int a[3], b[5];

/*@contract@*/
void increment(int x[], unsigned n) {
  x[n] += 1;
}

int main() {
  increment(a, 1);
  increment(b, 2);
  assert(a[1] == $at("Old", (int)(a[1])) + 1);
  assert(b[2] == $at("Old", (int)(b[2])) + 1);
  return 0;
}
