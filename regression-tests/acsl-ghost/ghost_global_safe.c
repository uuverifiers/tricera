//@ ghost int v;

/*@ requires v == 0;
    assigns v;
    ensures v == \old(v) + 1;
*/
void main() {
  //@ ghost v = v + 1;
}
