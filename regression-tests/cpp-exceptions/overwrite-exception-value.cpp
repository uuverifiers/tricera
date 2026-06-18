int main() {
    int x = 0;

    try {
        throw 1;
    } catch (int e) {
        try {
            throw 2;
        } catch (int e2) {
            x = e2;
        }
    }

    assert(x == 2);
}
