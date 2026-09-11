/*@
  requires \valid(p);
  ensures *p == \old(*p) + 1;
  assigns *p;
*/
void inc(int* p) {
    *p = *p + 2;
}

int main(void) {
    int a = 5;
    inc(&a);
    assert(a == 6);
    return 0;
}
