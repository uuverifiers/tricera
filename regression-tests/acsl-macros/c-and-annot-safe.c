// The same macro used in C code and in an annotation (run with -cpp).
#include <assert.h>
#define GOOD(x) ((x) >= 240)

int main(void) {
  int x = 250;
  assert(GOOD(x));
  //@ assert GOOD(x);
  return 0;
}
