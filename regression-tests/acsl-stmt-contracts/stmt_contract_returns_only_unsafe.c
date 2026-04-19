int abs(int x) {
  /*@ requires 1 == 1;
      ensures  \false;
      returns  ((x >= 0 && \result == x) || (x < 0 && \result == -x));
      assigns  \nothing;
  */
  {
    if (x >= 0) return x;
    return x;
  }
}

int main() {
  int a = abs(-7);
  //@ assert a == 7;
  return 0;
}
