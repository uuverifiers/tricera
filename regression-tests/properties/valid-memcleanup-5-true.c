#include <stdlib.h>

int main() {
  int *p = malloc(sizeof(int));
  free(p);
  exit(0);
}
