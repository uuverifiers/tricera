int subOne(int x){
  return x - 1;
}

int addOne(int x) {
  return x + 1;
}

void main() {
  int x;
  int y = 1;
  assume(x == subOne(y));
  assert(addOne(x) == 0);
}
