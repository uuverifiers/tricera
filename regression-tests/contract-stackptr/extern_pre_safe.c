/*@
  requires *p > 0;
  ensures *p == \old(*p) + 1;
  assigns *p;
*/
extern void incpos(int* p);

int main(void) {
    int a = 3;
    incpos(&a);
    assert(a == 4);
    return 0;
}
