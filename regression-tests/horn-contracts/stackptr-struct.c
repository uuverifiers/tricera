typedef struct {
  int val;
} S;

/*@contract@*/ 
void incr(S* t) {
    t->val++;
}

int main() {
    int init = _;
    S s = {init};

    incr(&s);

    assert(s.val == init+1);

    return 0;
}
