typedef struct {
    unsigned int val;
} S;

extern int non_det_int();

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
    unsigned int init = non_det_int();
    S s = {init};
 
    assume(init < 4294967295);

    incdec(&s);

    assert(s.val == init);
    return 0;
}
