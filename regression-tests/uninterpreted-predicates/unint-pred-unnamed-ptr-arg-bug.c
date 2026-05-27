/*$ P(int *) $*/

int* nondet_ptr();

void main() {
  int *p = 0;
  assert(P(p));

  int *q = nondet_ptr();
  assume(P(q));
  
  assert(p == q);
}
