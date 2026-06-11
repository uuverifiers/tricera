void foo(int x) {
    throw 10;
}

int main() {
    int x;
    try {
        foo();
    } catch (int e) {
        x = e;
    }

    assert(x == 10);

    return 0;
}