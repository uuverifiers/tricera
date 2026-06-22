/*@
  requires *p > 0;
  ensures *p == \old(*p) + 1;
  assigns *p;
*/
extern void incpos(int* p);

int main(void) {
    int a = 0;
    incpos(&a);
    assert(a == 1);
    return 0;
}
