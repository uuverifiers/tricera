#include <stdlib.h>
extern int nondet();

void main() {
    int n = nondet();
    assume(n > 0);
    int *arr = (int*) malloc(sizeof(int)*n);
    arr[n-1] = 42;
    free(arr);
}
