
/* Nondeterministically initialized by command line option -forceNondetInit. */
int a[5];

void main() {
    // Should be UNSAFE
    assert(a[1] == 0);
}
