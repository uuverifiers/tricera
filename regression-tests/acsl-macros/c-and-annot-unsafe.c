// The same macro used in C code and in an annotation (run with -cpp).
// UNSAFE: the C assertion holds (x == 250) but the ACSL one fails (x == 230).
#include <assert.h>
#define GOOD(x) ((x) >= 240)

int main(void) {
  int x = 250;
  assert(GOOD(x));
  x = x - 20;
  //@ assert GOOD(x);
  return 0;
}
