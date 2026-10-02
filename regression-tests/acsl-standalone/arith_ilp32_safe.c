typedef long tS32;

void foo(void) {
  int h = 2;
  tS32 r = 60 * 60 * ((tS32) 1000);
  tS32 t = (tS32)(h * 60 * ((tS32) 1000));
  //@ assert r == ((tS32) (60 * 60 * ((tS32) 1000)));
  //@ assert r == 3 * ((tS32) 1200000);
  //@ assert t == (tS32)(h * 60 * ((tS32) 1000));
}
