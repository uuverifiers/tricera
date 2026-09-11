/*@contract@*/
void f(int* p, int* q) {
    *p = 1;
    *q = 2;
}

int main() {
    int a[5];
    int i = 0;
    int j = 0;
    // &a[i], &a[j] may or may not alias (i==j?): cannot be decided syntactically.
    f(&a[i], &a[j]);
    assert(a[0] == 2);
    return 0;
}
