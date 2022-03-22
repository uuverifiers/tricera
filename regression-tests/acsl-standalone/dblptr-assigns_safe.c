// SAFE

int g = 42;

/*@
  requires \valid(p, q, *q);
  assigns *p;
  assigns **q;
  assigns g;
*/
void foo(int* p, int** q) {
  *p  = 42;
  **q = 42;
  g   = 42;
}
