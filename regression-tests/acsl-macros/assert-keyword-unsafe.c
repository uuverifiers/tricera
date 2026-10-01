// With -cpp, <assert.h> defines a function-like macro 'assert'. The ACSL
// keyword 'assert' in the annotation must not be expanded by it.
// UNSAFE: x == 0.
#include <assert.h>

int main(void) {
  int x = 0;
  //@ assert (x > 0);
  return 0;
}
