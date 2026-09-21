/*@contract@*/
int read(int *p) { return *p; }

int main() {
    int a[2] = {1, 2};
    int *p = a + 1;
    assert(read(p) == 2);
}
