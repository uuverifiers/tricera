#include <stdlib.h>

struct S1
{
  struct S1* f1;
};

struct S2
{
  struct S1* f2;
};

int main()
{
  struct S2 s2;
  struct S1 **p = malloc(sizeof(s2.f2)); // p is S1**, s2.f2 is S1*
  *p = malloc(sizeof(*s2.f2));  // *p is S1*, *s2.f2 is S1
  s2.f2 = *p;
  s2.f2->f1 = *p; // lhs is S1*, rhs is also S1*
  return 0;
}
