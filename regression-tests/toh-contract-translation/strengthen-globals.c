int required = 5;
int counter = 2;
int unchanged = 7;

/*@contract@*/
int increment(int n) {
  assert(required == 5);
  counter++;
  return n + 1;
}

int main() {
  assert(increment(1) == 2);
  assert(required == 5 && counter == 3 && unchanged == 7);
  return 0;
}
