// A regular local C variable may not share its name with a ghost
// global.
//@ ghost int v;

int main() {
  int v = 5;
  return v;
}
