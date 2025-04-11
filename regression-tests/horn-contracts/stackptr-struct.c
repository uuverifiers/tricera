typedef struct {
  int val;
} S;

extern int non_det_int();

/*@contract@*/
void incr(S* t) {
    t->val++;
}

int main() {
    int init = non_det_int();
    S s = {init};

    assume(-2147483648 < init && init < 2147483647);

    incr(&s);

    assert(s.val == init+1);

    return 0;
}
