// Regular C `assert()` over a ghost variable with a false predicate.
//@ ghost int v;

int main() {
  //@ ghost v = 5;
  assert(v == 99);
  return 0;
}
