#include <stdlib.h>
int main() {
  int *a = malloc(sizeof(int) * 2);
  int *b = a + 1;
  free(b - 1);
  return 0;
}
