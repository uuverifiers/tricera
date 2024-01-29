#include <stdlib.h>
extern int nondet();

void main() {
    int n = nondet();
    int *arr = (int*) malloc(sizeof(int)*n);
    arr[n] = 42;
    free(arr);
}
