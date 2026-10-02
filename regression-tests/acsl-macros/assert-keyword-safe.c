// With -cpp, <assert.h> defines a function-like macro 'assert'. The ACSL
// keyword 'assert' in the annotation must not be expanded by it.
#include <assert.h>

int main(void) {
  int x = 1;
  //@ assert (x > 0);
  return 0;
}
