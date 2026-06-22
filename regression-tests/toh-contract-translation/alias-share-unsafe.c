/*@contract@*/
void f(int* p, int* q) {
    *p = 1;
    *q = 2;
}

int main() {
    int x = 0;
    f(&x, &x);
    // p and q alias x, so x ends up 2, not 1: this assertion fails.
    assert(x == 1);
    return 0;
}
