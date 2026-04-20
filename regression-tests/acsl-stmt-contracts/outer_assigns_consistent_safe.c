int g;

/*@ requires \true;
    ensures  \result == 42 && g == 999;
    assigns  g;
*/
int f() {
  /*@ requires \true;
      ensures  \false;
      returns  \result == 42 && g == 999;
      assigns  g;
  */
  { g = 999; return 42; }
  return 0;
}

int main() {
  g = 0;
  int r = f();
  //@ assert r == 42;
  //@ assert g == 999;
  return 0;
}
