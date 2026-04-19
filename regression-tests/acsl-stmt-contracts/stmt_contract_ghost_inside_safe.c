//@ ghost int g = 0;

int main() {
  int x = 0;
  /*@ requires x == 0 && g == 0;
      ensures  x == 1 && g == \old(g) + 1;
  */
  {
    //@ ghost g = g + 1;
    x = x + 1;
  }
  //@ assert x == 1 && g == 1;
  return 0;
}
