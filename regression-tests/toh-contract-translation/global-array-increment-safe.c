/*
  Tests that nondeterministically
  initialized arrays are translated correctly.
 */
int a[3];

/*@contract@*/
void increment(int x[], unsigned n) {
  x[n] += 1;
}

/*@
  assigns a[1];
  ensures a[1] == \old(a[1]) + 1;
*/
void main() {
  increment(a, 1);
}
