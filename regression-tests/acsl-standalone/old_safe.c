// SAFE because assign to *p occurs after assign to g.
int g = 0;

/*@
  requires \valid(p);
  ensures g == \old(g) + \old(*p);
*/
void foo(int* p) {
  g += *p;
  *p = 42;
}
