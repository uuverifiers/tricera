int lookup(int key, int def) {
  /*@ requires \true;
      ensures  (key != 7 ==> \true) && (key == 7 ==> \false);
      returns  (key != 7 ==> \false) && (key == 7 ==> \result == 100);
      assigns  \nothing;
  */
  {
    if (key == 7) return 100;
  }
  return def;
}

int main() {
  int v;
  v = lookup(7, -1);
  //@ assert v == 100;
  v = lookup(3, -1);
  //@ assert v == -1;
  return 0;
}
