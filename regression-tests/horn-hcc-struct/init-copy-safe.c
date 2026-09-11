struct A {
    int x;
};

struct B {
    struct A a;
};

int main() {
    struct A aa = {4};
    struct B bb = {aa};
    assert(bb.a.x == aa.x);
    return 0;
}
