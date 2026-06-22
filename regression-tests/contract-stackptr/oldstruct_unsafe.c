struct P { int x; int y; };

/*@
  requires \valid(p);
  ensures p->x == \old(p->x) + \old(p->y);
  ensures p->y == \old(p->y);
  assigns *p;
*/
void addy(struct P* p) {
    p->x = p->x + p->y;
    p->y = p->y + 1;
}

int main(void) {
    struct P s;
    s.x = 4;
    s.y = 7;
    addy(&s);
    assert(s.x == 11);
    assert(s.y == 7);
    return 0;
}
