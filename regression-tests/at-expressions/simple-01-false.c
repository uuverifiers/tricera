int main() {
  int x = 0;
  int y = 3;

L1: // x = 0;
  x = 42;

L2:; // x = 42; y = 3;
  x = 3;
  
  assert($at(L1, (int)(x+5)) == 5);
  assert($at(L2, (int)(x+y)) == 43);
  assert(x == 3);
}