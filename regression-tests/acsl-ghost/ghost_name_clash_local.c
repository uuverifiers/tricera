// A regular local C variable may not share its name with a ghost
// global. Expect a declaration-time error, not SAFE/UNSAFE.
//@ ghost int v;

int main() {
  int v = 5;
  return v;
}
