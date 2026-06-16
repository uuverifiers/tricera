int main() {
    int x;

    try {
        x = 1;
        try {
            x = 2;
            throw 10;
        } catch (char) {
            x = 3;
        }
    } catch (int) { // should be caught here
        x = 4;
    } catch (long  n) {
        x = 5;
    }

    assert(x == 4);
    return 0;
}
