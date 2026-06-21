int main() {
    int x = 0;

    try {
        try {
            try {
                throw 9;
            } catch (int e) {
                throw;
            }
        } catch (int e) {
            e = 10; // this should not matter
            throw;
        }
    } catch (int e) {
        x = e;
    }

    assert(x == 9);
}
