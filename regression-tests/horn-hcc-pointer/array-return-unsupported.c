/*@contract@*/
int *identity(int p[]) { return p; }

int main() {
    int a[2] = {1, 2};
    int *p = identity(a);
    assert(*p == 1);
}
