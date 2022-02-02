/*@
  requires \valid(p);
  assigns \nothing;
  ensures \result == 42;
*/
int foo(int* p) {
  *p = 42;
  return 42;
}
