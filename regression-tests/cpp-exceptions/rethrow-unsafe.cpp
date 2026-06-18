int foo() {
    try {
        throw 1;
    } catch (...) {
        throw;
    }

    return 2;
}

int main() {
    int x;
    try {
        x = foo();
    } catch (char) {}
    return 0;
}