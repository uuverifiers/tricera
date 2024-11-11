int x;
/*@
  requires x >= 0;
  ensures x >= 2;
*/
void foo();

void main() {
  foo();
  assert(x >= 3);
}
