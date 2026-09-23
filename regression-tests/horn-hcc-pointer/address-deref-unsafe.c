#include <stdlib.h>
/*@contract@*/
int update(int *p, int *q) { *p = 1; *q = 2; return *p; }
int main() {
    int *q = malloc(sizeof(int));
    *q = 0;
    assert(update(&*q, q) == 1);
}
