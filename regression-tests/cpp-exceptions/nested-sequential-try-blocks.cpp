int main() {
    int x;
    int y;
    int z;

    try {
        x = 1;

        try {
            throw 1;
        } catch (char) {
            x = 2;
        } catch (int) {
            x = 3;
        }

        try {
            y = 2; 
        } catch (...) {
            y = 3;
        }

        throw 10;

    } catch (long) {
        z = 1;
    } catch (int) {
        z = 2;
    }

    try {
        throw 1;
    } catch (int) {} catch (char) {}

    assert(x == 3);
    assert(y == 2);
    assert(z == 2);

    return 0;
}
