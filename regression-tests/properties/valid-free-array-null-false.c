#include <stdlib.h>
int main() {
  int *p = malloc(sizeof(int) * 2);
  free(p);
  free(p);
  return 0;
}
