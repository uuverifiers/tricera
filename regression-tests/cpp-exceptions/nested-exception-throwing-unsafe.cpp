int main() {
    int x = 0;

    try {
        try {
            try {
                throw 9;
            } catch (int e) {
                throw e;
            }
        } catch (int e) {
            throw 5; // new value thrown
        }
    } catch (int e) {
        x = e;
    }

    assert(x == 9);
}
