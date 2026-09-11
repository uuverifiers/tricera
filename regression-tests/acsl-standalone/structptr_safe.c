struct S { int x; };

/*@
  requires \valid(p);
  requires p->x == 42;
  ensures \result == 42;
*/
int foo(struct S* p) {
  return p->x;
}
