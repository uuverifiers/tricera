//@ ghost int count = 0;

int main() {
  /*@ ghost int i = 0;
             while (i < 5) {
               i = i + 1;
               count = count + 1;
             }
  */
  //@ assert count == 5;
  return 0;
}
