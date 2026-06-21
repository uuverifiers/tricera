struct Inner { int v; };
struct Outer { struct Inner* in; };
/*@
  requires \valid(p);
  requires \valid(p->in);
  requires p->in->v == 7;
  ensures  \result == 8;
*/
int foo(struct Outer* p) { return p->in->v; }
