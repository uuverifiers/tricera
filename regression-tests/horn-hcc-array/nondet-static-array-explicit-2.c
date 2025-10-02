
void main() {
    static int a[5] = _;

    // Should be UNSAFE - but is currently SAFE 2025-10-02. Needs extension of theory.
    assert(a[0] == a[1]);
}
