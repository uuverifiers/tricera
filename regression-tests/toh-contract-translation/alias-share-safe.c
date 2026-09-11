/*@contract@*/
int f(int* p, int* q) {
    *p = 1;
    *q = 2;
    return *p;
}

int main() {
    int x = 0;
    int r = f(&x, &x);
    // p and q alias x, so *q = 2 also sets *p; r must be 2.
    assert(r == 2);
    return 0;
}
