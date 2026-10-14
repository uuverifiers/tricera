#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
int main() {
  int *p = malloc(sizeof(int));
  *p = 1;
  int *q;
  q = __VERIFIER_nondet_int() ? p : 0;
  if (q) assert(*q != 1);
  return 0;
}
