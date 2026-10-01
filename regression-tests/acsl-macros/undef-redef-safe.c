// #undef and redefinition between two annotations. Each annotation must be
// expanded with the definition in effect at its position: if the last
// definition (V == 2) were used everywhere, the first assertion would fail.
#define V 1

int main(void) {
  int x = 1;
  //@ assert x == V;
#undef V
#define V 2
  x = 2;
  //@ assert x == V;
  return 0;
}
