int main() {
  //@ ghost integer m = 4294967301;
  //@ ghost int g = 0;
  //@ ghost g = m;
  //@ assert g != 5;
  return 0;
}
