#include <stdlib.h>
int *g;
/*@contract@*/
int reset() {
    int value = *g;
    g = 0;
    return value;
}
int main() {
    g = malloc(sizeof(int));
    *g = 7;
    assert(reset() == 7);
}
