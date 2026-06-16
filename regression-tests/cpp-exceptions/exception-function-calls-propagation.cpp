int bar() {
    throw 'c';
}

int foo() {
    try {
        bar();
    } catch (int) {}
    return 1;
}

int main() {
    int y = 42;
    try {
        y = foo();
    } catch (char) {}

    assert(y == 42);
}
