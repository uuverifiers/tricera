int subOne(int x){
  return x - 1;
}

int addOne(int x) {
  return x + 1;
}

void main() {
  int x;
  int y = 1;
  assume(x == (y > 0 ? addOne(y) : (subOne(y)+1)));
  assert(x == (y <= 0 ? addOne(y) : (subOne(y)+1)));
}
