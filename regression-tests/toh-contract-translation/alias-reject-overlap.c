struct S {
    int x;
};

/*@contract@*/
void f(struct S* p, int* q) {
    p->x = 1;
    *q = 2;
}

int main(void) {
    struct S s;
    // &s and &s.x overlap: cannot be decided as distinct.
    f(&s, &s.x);
    assert(s.x == 2);
    return 0;
}
