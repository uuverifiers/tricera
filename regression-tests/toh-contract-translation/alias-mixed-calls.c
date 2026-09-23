/*@contract@*/
int update(int *p, int *q, int step) {
  ++*p;
  *q += step;
  return *p;
}

/*@contract@*/
int twice(int n) { return 2*n; }

int main() {
  int shared = 2, left = 2, right = 5;
  assert(update(&shared, &shared, 3) == 6);
  assert(shared == 6);
  assert(update(&left, &right, 4) == 3);
  assert(left == 3 && right == 9);
  assert(twice(7) == 14);
}
