typedef struct {
    int val;
} S;


/*@contract@*/ 
void mod(S* t1, S* t2) {
    t1->val++;
    t2->val--;
}

int main() {
    int init = _;
    S s1 = {init};
    S* s2 = malloc(sizeof(S));
    s2->val = init;

    mod(&s1, s2);

    assert(s1.val == init+1 && s2->val == init-1);

    return 0;
}