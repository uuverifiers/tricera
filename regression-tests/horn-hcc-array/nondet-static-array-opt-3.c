
void main() {
    /* Nondeterministically initialized by command line option -forceNondetInit. */
    static int a[5];
    static int b[5];

    assume(a[0] == b[0]);

    // Should be UNSAFE - but is currently SAFE 2025-10-02. Needs extension of theory.
    assert(a[1] == b[1]);
}
