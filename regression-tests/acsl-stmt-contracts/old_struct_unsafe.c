struct S { int f; };

int main() {
  struct S s;
  s.f = 10;
  /*@ requires s.f >= 0;
      ensures  s.f == \old(s.f) + 1;
  */
  { s.f = s.f + 2; }
  return 0;
}
