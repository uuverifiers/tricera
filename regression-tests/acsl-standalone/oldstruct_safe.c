struct S { int x; };
/*@
  requires \valid(p);
  assigns  \nothing;
  ensures  p->x == \old(p->x);
*/
void foo(struct S* p) { }
