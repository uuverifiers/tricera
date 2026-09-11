struct S { int arr[5]; };
/*@
  requires \valid(p);
  requires p->arr[2] == 7;
  ensures  \result == 8;
*/
int foo(struct S* p) { return p->arr[2]; }
