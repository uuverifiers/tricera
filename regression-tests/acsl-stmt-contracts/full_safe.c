int main() {
  int r = 0;
  /*@ requires r >= 0 && r <= 1000;
      ensures  r == \old(r) + 1;
      assigns  r;
  */
  { r = r + 1; }
  //@ assert r >= 1 && r <= 1001;
  return 0;
}
