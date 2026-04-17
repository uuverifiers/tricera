// Regular C `assume()` sees ghost variables and acts on the spec path.
// If `assume(v == 5)` compiles and is treated as a spec assumption,
// the following `//@ assert v == 5;` must pass trivially.
//@ ghost int v;

int main() {
  assume(v == 5);
  //@ assert v == 5;
  return 0;
}
