#include <stdlib.h>

void main() {
  int *p = malloc(sizeof(int)*10);
  // This violates memcleanup, but not memtrack.
  // Note, if there would have been a return statement, this would
  // have violated memtrack too.
  // See https://groups.google.com/g/sv-comp/c/Slug4p2DACM/m/ajhC7krvEgAJ
}
