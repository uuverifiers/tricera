int main() {
  int i = 0;
  /*@ requires i == 0;
      ensures  i == 1;
  */
  i = i + 1;
  //@ assert i == 1;
  return 0;
}
