typedef struct {
    unsigned int val;
} S;

/*@contract@*/
void decr(S* q) {
  q->val--;
}

/*@contract@*/ 
void incdec(S* p) {
    p->val++;
    decr(p);
}


int main() {
    unsigned int init = _;
    S s = {init};
 
    incdec(&s);

    assert(s.val == init);
    return 0;
}
