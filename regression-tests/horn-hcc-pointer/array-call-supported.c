/*@contract@*/
int read_array(int p[]) { return p[1]; }

/*@contract@*/
int read_scalar(int *p) { return *p; }

int read_inline(int *p) { return *p; }

int main() {
    int a[3] = {10, 20, 30};
    int *q = a + 1;
    assert(read_array(a) == 20);
    assert(read_array(q) == 30);
    assert(read_inline(a + 1) == 20);
    int *p = malloc(sizeof(int));
    *p = 42;
    assert(read_scalar(p) == 42);
}
