/*@
  requires \valid(p);
  requires n >= 0;
  ensures *p == \old(*p) + n;
  assigns *p;
*/
void addn(int* p, int n) {
    *p = *p + n + 1;
}

int main(void) {
    int a = 5;
    addn(&a, 3);
    assert(a == 8);
    return 0;
}
