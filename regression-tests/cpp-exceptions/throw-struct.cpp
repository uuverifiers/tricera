struct S {
    int n;
};

int main() {
    int x = 0;
    try {
        struct S s;
        s.n = 10;
        throw s;
    } catch (S e) {
        x = e.n;
    }
    assert(x == 10);
}