int main() {
  //@ ghost boolean t = \true;
  //@ ghost boolean f = \false;
  assert(t == 1);
  assert(f == 0);
  return 0;
}
