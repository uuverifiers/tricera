/*@
  requires \valid(a) && \valid(b);
  assigns  *a, *b;
  ensures  (*a) == \old(*b);
  ensures  (*b) == \old(*a);
*/
void foo(int* a, int* b) {
  int tmp = *a;
  *a = *b;
  *b = tmp;
}
