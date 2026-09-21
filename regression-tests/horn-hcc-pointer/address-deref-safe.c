#include <stdlib.h>
/*@contract@*/
int update(int *p, int *q) { *p = 1; *q = 2; return *p; }
int main() {
    int *empty = 0;
    assert(&*empty == 0);
    int *q = malloc(sizeof(int));
    *q = 0;
    assert(update(&*q, q) == 2);
    int *alias = &*q;
    assert(update(alias, q) == 2);
}
