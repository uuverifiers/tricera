// Multiple ghost statements in a single block: the second statement
// sees the state left by the first.
//@ ghost int x;

int main() {
  /*@ ghost x = 1;
             x = x + 1;
  */
  //@ assert x == 2;
  return 0;
}
