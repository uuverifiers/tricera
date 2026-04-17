//@ ghost int v;

/*@ requires v == 0;
    assigns v;
    ensures v == \old(v) + 2;
*/
void main() {
  //@ ghost v = v + 1;
}
