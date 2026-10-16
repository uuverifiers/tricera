#include <stdlib.h>
int main() {
  int *p = malloc(sizeof(int));
  int *q = p + 1;
  return 0;
}
