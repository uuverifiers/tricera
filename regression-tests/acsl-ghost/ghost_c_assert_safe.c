//@ ghost int v;

int main() {
  //@ ghost v = 5;
  assert(v == 5); // regular assert()` sees ghost variables
  return 0;
}
