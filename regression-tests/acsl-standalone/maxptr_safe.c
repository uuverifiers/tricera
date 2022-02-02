/*@ 
  requires \valid(p, q);
  ensures ((\result == *p) || (\result == *q));
  ensures \result >= (*p);
  ensures \result >= (*q);
*/
int foo(int* p, int* q) {
  if (*p >= *q) {
    return *p;
  } else {
    return *q;
  }
}
