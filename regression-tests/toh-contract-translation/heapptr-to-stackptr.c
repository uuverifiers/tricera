#include <stdlib.h>

/*@contract@*/
void swap(int *volatile* x, int *volatile* y){
    int *volatile tmp = *x;
    int tmp2 = *tmp;
    *x = *y;
    *y = tmp;
}

void main() {
  int *volatile a = malloc(sizeof(int));
  int *volatile b = malloc(sizeof(int));
  *b = 42;
  swap(&a, &b);
//  assert(*a == 42 && *b == 0);
}

