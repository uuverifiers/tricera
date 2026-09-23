#include <stdlib.h>

/*@contract@*/
int release(int *p) {
    int value = *p;
    free(p);
    return value;
}

int main() {
    int *p = malloc(sizeof(int));
    *p = 7;
    assert(release(p) == 7);
}
