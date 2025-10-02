
void main() {
    static int a[5] = _;

    // Should be UNSAFE
    assert(a[0] == 0);
}
