#include <stdlib.h>

int main() {
    int *p = malloc(sizeof(int));
    // p is not freed before program end - violates memcleanup.
    // int main with no return value, this triggers a different exit in CCReader
}
