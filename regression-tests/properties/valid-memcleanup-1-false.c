#include <stdlib.h>

void main() {
    int *p = malloc(sizeof(int));
    // p is not freed before program end - violates memcleanup.
}
