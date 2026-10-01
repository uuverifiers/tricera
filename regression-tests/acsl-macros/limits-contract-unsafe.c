// Macro from a system header (INT_MAX) used in a contract. Needs -cpp.
// UNSAFE: x == INT_MAX satisfies the precondition but \result > INT_MAX.
#include <limits.h>

/*@ requires x <= INT_MAX;
    ensures \result == x + 1;
    ensures \result <= INT_MAX;
*/
int inc(int x) {
  return x + 1;
}
