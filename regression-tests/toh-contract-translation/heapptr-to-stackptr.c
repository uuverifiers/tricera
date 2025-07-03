#include <stdlib.h>

/*@contract@*/
void swap(int **x, int **y){
    int *tmp = *x;
    *x = *y;
    *y = tmp;
}

void main() {
  int *a = malloc(sizeof(int));
  int *b = malloc(sizeof(int));
  *a = 0;
  *b = 2;
  swap(&a, &b);
  assert(*a == 2 && *b == 0);
}
