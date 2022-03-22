// UNSAFE because assign to *p occurs before assign to g.
int g = 0;

/*@
  requires \valid(p);
  ensures g == \old(g) + \old(*p);
*/
void foo(int* p) {
  *p = 42;
  g += *p;
}
