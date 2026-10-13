int main() {
  int x = 3;
  //@ ghost boolean b = x > 2;
  //@ assert !b;
  return 0;
}
