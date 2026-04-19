struct S { int f; };

int main() {
  struct S s;
  s.f = 5;
  /*@ contract @*/
  { s.f = s.f + 1; }
  //@ assert s.f == 6;
  return 0;
}
