struct S { int x; };

/*@
  requires \valid(p);
  ensures p->x == \old(p->x) + 1;
  assigns *p;
*/
void incx(struct S* p) {
    p->x = p->x + 1;
}

int main(void) {
    struct S s;
    s.x = 10;
    incx(&s);
    assert(s.x == 11);
    return 0;
}
