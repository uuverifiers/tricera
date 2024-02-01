#include <stdlib.h>

extern int nondet();
int main() {
    int *p = malloc(sizeof(int));
    // p is not freed before program end - violates memcleanup.
    // int main with multiple exit paths
    abort();
    free(p);
}
