
/* Nondeterministically initialized by command line option -forceNondetInit. */
int a[5];
int b[5];

void main() {
    assume(a[0] == b[0]);

    // Should be UNSAFE - but is currently SAFE 2025-10-02. Needs extension of theory.
    assert(a[1] == b[1]);
}
