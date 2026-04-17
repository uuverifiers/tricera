// Regular C code must not see ghost variables.
//@ ghost int v;

int main() {
  return v;
}
