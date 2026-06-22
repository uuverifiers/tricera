/*@
  requires \valid(p);
  ensures *p == \old(*p) + 1;
  assigns *p;
*/
extern void inc(int* p);

int main(void) {
    int a = 5;
    inc(&a);
    assert(a == 6);
    return 0;
}
