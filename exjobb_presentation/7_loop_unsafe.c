void main() {
  int i = 0;
  float x = 0.5f;
  float y = x;
  while (x < 3000.0f) {
    x = x*2.0f;
    ++i;
  }
  assert(x==y);
}

