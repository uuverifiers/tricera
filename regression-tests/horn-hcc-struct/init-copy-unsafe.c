struct A {
    int x;
};

struct B {
    struct A a;
};

int main() {
    struct A aa = {4};
    struct B bb = {aa};
    assert(bb.a.x == 5);
    return 0;
}
