struct S { int x; };
/*@
  requires \valid(p);
  assigns  \nothing;
  ensures  p->x == \old(p->x) + 1;
*/
void foo(struct S* p) { }
