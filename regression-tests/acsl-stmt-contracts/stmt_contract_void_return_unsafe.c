int g;

void incr() {
  /*@ requires g >= 0;
      ensures  g == \old(g) + 1;
      returns  g == \old(g) + 1;
  */
  {
    if (g == 0) { g = 2; return; }
    g = g + 1;
  }
}

int main() {
  g = 0;
  incr();
  //@ assert g == 1;
  return 0;
}
