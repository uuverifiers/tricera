typedef struct {
    int val;
} S;

extern int non_det_int();

/*@contract@*/
void incr(S* t) {
    t->val++;
}


void entryPoint(void) {
    int init = non_det_int();

    assume(-2147483648 <= init && init < 2147483647);

    S s = {init};
    incr(&s);

    assert(s.val == init+1);
}
