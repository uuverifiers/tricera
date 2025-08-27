int g = 10;

void f(int p) {
  // Pre / Old: p == 5, g == 10.
  
  p = 20;
  g = 30;
  // p = 20, g = 30

  assert($at(Pre, (int)(p)) == 10);
 
  g = 5;
}

void main() {
  f(5);
  assert(g == 5);
}