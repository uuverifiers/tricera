//@ ghost int x = 0;
//@ ghost int y = x + 1;

int main() {
  //@ assert x == 0;
  //@ assert y == 1;
  return 0;
}
