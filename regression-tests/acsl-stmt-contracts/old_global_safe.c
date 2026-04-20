int g = 0;

int main() {
  /*@ requires g == 0;
      ensures  g == \old(g) + 1;
  */
  { g = g + 1; }
  //@ assert g == 1;
  return 0;
}
