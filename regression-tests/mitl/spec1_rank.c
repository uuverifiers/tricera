int x;

MITL_SPEC G(<1>F@[0,5] { x >= 0 }) ;
RANKING <1> x > 0 ;

extern int nondet();

thread A {
  clock c;
  c = 0;

  while(1) {
    x = nondet();
    progress (c <= 5) {
      if (x < 0) {
        x = - x;
      }
    }
  }
}
