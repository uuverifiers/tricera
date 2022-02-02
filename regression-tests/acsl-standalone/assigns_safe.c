/*@
  requires \valid(p);
  assigns \nothing;
  ensures \result == 42;
*/
int foo(int* p) {
  return 42;
}
