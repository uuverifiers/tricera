struct S {
    int x;
};

/*@contract@*/
void f(int* p, int* q) {
    *p = 1;
    *q = 2;
}

int main() {
    struct S s;
    struct S* p1 = &s;
    struct S* p2 = &s;
    // &p1->x, &p2->x may alias (p1==p2?): cannot be decided syntactically.
    f(&p1->x, &p2->x);
    assert(s.x == 2);
    return 0;
}
