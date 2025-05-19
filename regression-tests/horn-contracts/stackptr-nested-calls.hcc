typedef struct {
    int val;
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
    int init = non_det_int();
    S s = {init};
 
    assume(-2147483648 <= init && init < 2147483647);

    incdec(&s);

    assert(s.val == init);
    return 0;
}
