/*@
  requires \valid(p);
  ensures \result == *p;
*/
int foo(int* p) {
  return *p;
}
