// Regular C code must not see ghost variables. `v` is only declared
// as a ghost, so `return v;` should fail with an undeclared-identifier
// error (not SAFE/UNSAFE).
//@ ghost int v;

int main() {
  return v;
}
