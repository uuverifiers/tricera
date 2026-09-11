//@ ghost int v;

int main() {
  assume(v == 5);
  //@ assert v == 5;
  return 0;
}
