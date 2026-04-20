int g;

/*@ requires \true;
    ensures  \result == 42;
    assigns  \nothing;
*/
int f() {
  /*@ requires \true;
      ensures  \false;
      returns  \result == 42;
      assigns  g;
  */
  { g = 999; return 42; }
  return 0;
}

int main() {
  g = 0;
  int r = f();
  return 0;
}
