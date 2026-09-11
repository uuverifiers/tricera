/*@
  requires \valid(p);
  requires \valid(q);
  ensures *p == \old(*q);
  ensures *q == \old(*p);
  assigns *p, *q;
*/
void swap(int* p, int* q) {
    int t = *p;
    *p = *q;
    *q = *q;
}

int main(void) {
    int a = 5;
    int b = 9;
    swap(&a, &b);
    assert(a == 9);
    assert(b == 5);
    return 0;
}
