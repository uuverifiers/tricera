// #undef and redefinition between two annotations. Each annotation must be
// expanded with the definition in effect at its position.
// UNSAFE: the second assertion is x == 2 with x == 1. If the first
// definition (V == 1) were wrongly kept, this would be reported SAFE.
#define V 1

int main(void) {
  int x = 1;
  //@ assert x == V;
#undef V
#define V 2
  //@ assert x == V;
  return 0;
}
