struct S { int f; };
struct S s;

int main() {
  s.f = 0;
  /*@ requires s.f == 0;
      ensures  s.f >= 1 && s.f <= 10;
      assigns  s;
  */
  { s.f = 5; }
  //@ assert s.f == 5;
  return 0;
}
