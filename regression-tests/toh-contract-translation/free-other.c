#include <stdlib.h>

/*@contract@*/
int release(int *p, int *q) {
    free(q);
    return *p;
}

int main() {
    int *p = malloc(sizeof(int));
    int *q = malloc(sizeof(int));
    *p = 7;
    assert(release(p, q) == 7);
    assert(*p == 7);
    free(p);
}
