// Macros in function contracts, expected SAFE.
// - function-like and object-like macros in requires/ensures (clamp)
// - a macro named 'old' must not be expanded inside the built-in \old, but
//   must be expanded where it is a plain identifier (bump adds 1)
#define MAXV 10
#define IN_BOUNDS(r) ((r) >= 0 && (r) <= MAXV)
#define old 1

int g;

/*@ requires x >= 0;
    ensures IN_BOUNDS(\result);
*/
int clamp(int x) {
  if (x > 10)
    return 10;
  return x;
}

/*@ assigns g;
    ensures g == \old(g) + old;
*/
void bump(void) {
  g = g + 1;
}

int main(void) {
  int r = clamp(42);
  g = 0;
  bump();
  return 0;
}
