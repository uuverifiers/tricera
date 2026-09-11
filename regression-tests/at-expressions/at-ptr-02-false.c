#include <stdlib.h>

int **pp;

void main() {
  pp = malloc(sizeof(int *));
  *pp = malloc(sizeof(int));
  **pp = 3;
  L: ;
  **pp = 4;
  assert(**$at("L", (int **) pp) == 3);
}
