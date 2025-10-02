
/* Nondeterministically initialized by command line option -forceNondetInit. */
int a[5];

void main() {
    // Should be UNSAFE - but is currently SAFE 2025-10-02. Needs extension of theory.
    assert(a[0] == a[1]);
}
