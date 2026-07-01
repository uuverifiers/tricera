int dead_unused = 7;
int threshold   = 50;

/*@
  requires n <= threshold;
  assigns \nothing;
  ensures \result <= threshold;
*/
int clamp(int n) {
  return n;
}

int main() {
  int r = clamp(100);
  assert(r <= 50);
  return 0;
}
