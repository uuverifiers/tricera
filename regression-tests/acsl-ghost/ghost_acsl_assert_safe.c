// ACSL `//@ assert` referencing a ghost variable. Regression for the
// already-working spec-level path.
//@ ghost int v;

int main() {
  //@ ghost v = 5;
  //@ assert v == 5;
  return 0;
}
