// regex would keep 'field' from the annotation; parsing the ACSL does not
struct S { int field; };

int field = 99;

struct S gs;

int main(void) {
  gs.field = 5;
  gs.field = gs.field + 1;
  /*@ assert gs.field == 6; @*/
  assert(gs.field == 6);
  return 0;
}
