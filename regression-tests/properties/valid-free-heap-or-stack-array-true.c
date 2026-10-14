#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
int main() {
  int b[2];
  int c = __VERIFIER_nondet_int();
  int *p = c ? (int*) malloc(sizeof(int) * 2) : b;
  if (c) free(p);
  return 0;
}
