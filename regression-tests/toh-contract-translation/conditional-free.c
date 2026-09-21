#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

/*@contract@*/
int release(int *p, int flag) {
    int value = *p;
    if (flag) free(p);
    return value;
}

int main() {
    int *p = malloc(sizeof(int));
    *p = 7;
    int flag = __VERIFIER_nondet_int();
    assert(release(p, flag) == 7);
    if (!flag) free(p);
}
