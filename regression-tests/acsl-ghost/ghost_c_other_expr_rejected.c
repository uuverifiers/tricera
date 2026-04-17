// Regular C expression (non-assert/assume) may NOT reference a ghost
// variable. Expect an "Undeclared identifier" translation error.
//@ ghost int v;

int main() {
  int x = v + 1;
  return x;
}
