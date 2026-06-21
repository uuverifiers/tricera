int main() {
    int x = 0;
    int y = 0;

    try {
        x = 1;
        throw 4711;
        x = 10; // should not execute
    } catch (int e) {
        y = 2;
    }

    assert(x == 1);
    assert(y == 2);
    return 0;
}
