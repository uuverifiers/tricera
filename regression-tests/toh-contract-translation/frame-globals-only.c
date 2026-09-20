int count, unchanged;

/*@contract@*/
void increment() {
  int unchanged = 3;
  count += unchanged;
}

/*@contract@*/
int read_count() {
  return count;
}

int main() {
  count = 0;
  unchanged = 7;
  increment();
  assert(read_count() == 3);
  assert(unchanged == 7);
  return 0;
}
