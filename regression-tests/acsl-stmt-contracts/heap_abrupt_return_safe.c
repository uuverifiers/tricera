#include <stdlib.h>

int deref_or_default(int *p, int def) {
  /*@ requires \valid(p);
      ensures  \false;
      returns  (*p == 0 ==> \result == def) && (*p != 0 ==> \result == *p);
      assigns  \nothing;
  */
  {
    if (*p == 0) return def;
    return *p;
  }
  return 0;
}

int main() {
  int *q = malloc(sizeof(int));
  *q = 0;
  int r = deref_or_default(q, -1);
  //@ assert r == -1;
  *q = 42;
  r = deref_or_default(q, -1);
  //@ assert r == 42;
  return 0;
}
