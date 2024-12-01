int x;

/*@
  requires x >= 0;
  ensures \result > \old(x);
*/
int foo();


void main() {
  x = foo();
  assert(x >= 2);
}
