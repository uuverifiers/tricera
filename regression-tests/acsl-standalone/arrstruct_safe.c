struct S { int x; };
struct S g[5];
/*@
  requires \valid(&g[2]);
  requires g[2].x == 7;
  ensures  \result == 7;
*/
int foo(void) { return g[2].x; }
