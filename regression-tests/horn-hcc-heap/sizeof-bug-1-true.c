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
  s2.f2 = malloc(sizeof(*s2.f2));
  s2.f2->f1 = s2.f2;
  return 0;
}
