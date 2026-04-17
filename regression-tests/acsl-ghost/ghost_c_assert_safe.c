// Regular C `assert()` sees ghost variables (specification-like
// primitive in Tricera's extended C).
//@ ghost int v;

int main() {
  //@ ghost v = 5;
  assert(v == 5);
  return 0;
}
