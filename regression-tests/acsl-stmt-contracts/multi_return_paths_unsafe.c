int sign(int x) {
  int r = 0;
  /*@ requires r == 0;
      ensures  \false;
      returns  r == 0 &&
               ((x > 0 && \result == 1)
             || (x < 0 && \result == -1)
             || (x == 0 && \result == 0));
      assigns  \nothing;
  */
  {
    if (x > 0) return 999;
    if (x < 0) return -1;
    return 0;
  }
  return r;
}

int main() {
  int a = sign(5);
  //@ assert a == 1;
  return 0;
}
