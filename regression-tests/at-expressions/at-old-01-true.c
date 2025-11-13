int g = 10;

int f(int p) {
  // Pre / Old: p == 5, g == 10.
  
  p = 20;
  g = 30;
  // p = 20, g = 30

  assert($at("Pre", (int)(p + g)) == 15);
  assert($at("Old", (int)(p + g)) == 15);
 
  p = 3;
  g = 5;

  return p + g;
}

void main() {
  f(5);
  assert(g == 5);
}