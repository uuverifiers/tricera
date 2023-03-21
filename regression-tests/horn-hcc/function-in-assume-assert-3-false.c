int subOne(int x){
  int res = x - 1;
  return res;
}

int addOne(int x) {
  int res = x + 1;
  return res;
}

void main() {
  int x;
  int y = 1;
  assume(x == (y > 0 ? addOne(y) : (subOne(y)+1)));
  assert(x == (y <= 0 ? addOne(y) : (subOne(y)+1)));
}
