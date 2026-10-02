typedef long tS32;

void foo(void) {
  tS32 r = 60 * 60 * ((tS32) 1000);
  //@ assert r == ((tS32) (60 * 60 * ((tS32) 1001)));
}
