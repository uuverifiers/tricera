#include <stdlib.h>
int main() {
  int *p = malloc(sizeof(int) * 2);
  free(p);
  p = 0;
  free(p);
  return 0;
}
