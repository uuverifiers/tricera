#include <stdlib.h>

/*@contract@*/
void increment(int *p) {
    ++*p;
}

int main() {
    int *p = malloc(sizeof(int));
    int *q = malloc(sizeof(int));
    *p = 0;
    *q = 7;
    increment(p);
    assert(*p == 1);
    // The inferred contract must also preserve this unrelated cell.
    assert(*q == 7);
    return 0;
}
