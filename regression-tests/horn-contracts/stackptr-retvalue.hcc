typedef struct {
    unsigned int val;
} S;

/*@contract@*/ 
int* incr(S* t) {
    t->val++;
    return &(t->val);
}

int main() {
    S s = {0};
 
    // NOTE: 2025-03-27: This would fail due to the way stack
    // pointer support is implemented via rewriting to global variables.
    // However, TriCera interprets the return value as a heap pointer, and
    // recognizes the mix of heap and stackpointer and issues an 
    // "Unsupported" message.
    assert(incr(&s) == &(s.val));

    return 0;
}
