int validate(int x) {
  /*@ requires \true;
      ensures  (x < 0  ==> \false) && (x >= 0 ==> \true);
      returns  (x >= 0 ==> \false) && (x < 0  ==> \result == -1);
      assigns  \nothing;
  */
  {
    if (x < 0) return -1;
  }
  return 0;
}

int main() {
  int rc;
  rc = validate(10);
  //@ assert rc == 0;
  rc = validate(-3);
  //@ assert rc == -1;
  return 0;
}
