/*@contract@*/
int read(int *p) { return *p; }

int main() {
    int a[2] = {1, 2};
    assert(read(a + 1) == 2);
}
