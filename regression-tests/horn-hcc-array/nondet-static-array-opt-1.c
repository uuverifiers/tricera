
void main() {
    static int a[5]; // Nondeterministically initialized by command line option -forceNondet.

    // Should be UNSAFE
    assert(a[1] == 0);
}
