int f(int x) {
  /*@ requires \true;
      ensures  \true;
      returns  \result == 0;
      assigns  \nothing;
  */
  {
    /*@ requires \true;
        ensures  \true;
        returns  \result == 0;
        assigns  \nothing;
    */
    { if (x == 0) return 0; }
  }
  return 1;
}

int main() { f(0); return 0; }
