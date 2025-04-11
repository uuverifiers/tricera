#include <stdlib.h>

typedef struct {
    int val;
} S;

extern int non_det_int();

/*@contract@*/
void mod(S* t1, S* t2) {
    t1->val++;
    t2->val--;
}

int main() {
    int init = non_det_int();

    assume(-2147483648 < init && init < 2147483647);

    S s1 = {init};
    S* s2 = (S*) malloc(sizeof(S));

    assert(s2 != 0);

    s2->val = init;

    mod(&s1, s2);

    assert(s1.val == init+1 && s2->val == init-1);

    return 0;
}