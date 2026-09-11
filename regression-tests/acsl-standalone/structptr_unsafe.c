struct S { int x; };

/*@
  requires \valid(p);
  requires p->x == 42;
  ensures \result == 41;
*/
int foo(struct S* p) {
  return p->x;
}
