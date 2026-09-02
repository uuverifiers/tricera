struct S { int x; };

/*@
  ensures p->x == \old(p->x) + 1;
  assigns *p;
*/
extern void incx(struct S* p);

int main(void) {
    struct S s;
    s.x = 10;
    incx(&s);
    assert(s.x == 12);
    return 0;
}
