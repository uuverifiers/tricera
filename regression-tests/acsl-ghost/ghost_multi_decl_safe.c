// Multi-declaration block: `int y = x + 1;` references `x`
// declared earlier in the same block.
/*@ ghost int x = 0;
           int y = x + 1;
*/

int main() {
  //@ assert x == 0;
  //@ assert y == 1;
  return 0;
}
