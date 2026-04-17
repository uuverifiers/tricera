//@ ghost int v;

/*@ requires v == 0;
    assigns v;
    ensures v == 5;
*/
void main() {
  //@ ghost int tmp = 5;
  //@ ghost v = tmp;
}
