#include <stdlib.h>

extern int nondet();
int main() {
    int *p = malloc(sizeof(int));
    // p is not freed before program end - violates memcleanup.
    // int main with multiple exit paths
    if(nondet()) {
      free(p);
      return 0;
    } else {
      free(p);
    } // p is freed on all paths, this is safe.
}
