/*@
  ensures *p == \old(*q) + 1;
  assigns *q;
*/
extern void g(int* p, int* q);

int main(void) {
    int x = 5;
    g((int*)(&x), &x);
    assert(x == 6);
    return 0;
}
