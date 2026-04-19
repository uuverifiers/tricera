int g;

void bump() {
  /*@ requires g >= 0;
      ensures  g == \old(g) + 1;
  */
  { g = g + 1; }
}

int main() {
  g = 0;
  bump();
  //@ assert g == 1;
  return 0;
}
