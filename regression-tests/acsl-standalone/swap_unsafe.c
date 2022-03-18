// FIXME: Currently gives error when producing CEX. Update answer when fixed.

/*@
  requires \valid(a) && \valid(b);
  assigns  *a, *b;
  ensures  (*a) == \old(*b);
  ensures  (*b) == (*a);
*/
void foo(int* a, int* b) {
  int tmp = *a;
  *a = *b;
  *b = tmp;
}
