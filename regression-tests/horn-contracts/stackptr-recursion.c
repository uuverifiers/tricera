typedef struct {
    unsigned int val;
} S;


/*@contract@*/ 
void incr(S* t) {
    t->val++;
    if (t->val < 5) {
      incr(t);
    }
}

int main() {
    S s = {0};
 
    incr(&s);

    assert(s.val == 4);

    return 0;
}
