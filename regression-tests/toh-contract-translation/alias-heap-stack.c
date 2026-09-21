#include <stdlib.h>
/*@contract@*/
int update(int *p, int *q) { ++*p; --*q; return *p; }
/*@contract@*/
void bump(int *r) { ++*r; }
int main() {
 int spare = 10; bump(&spare); assert(spare == 11);
 int local = 2;
 int *q = malloc(sizeof(int)); *q = 5;
 assert(update(&local, q) == 3);
 assert(local == 3 && *q == 4);
}
