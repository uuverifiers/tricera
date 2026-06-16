int main() {
    int x = 0;
    try {
        x = 1;
    } catch (int e) {
        x = 2;
    }
    assert(x == 1);
}
