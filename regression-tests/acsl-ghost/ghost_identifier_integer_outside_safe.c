int integer = 5;
int boolean = 0;

int main() {
  integer = integer + 1;
  boolean = !boolean;
  /*@ ghost int g = 0; */
  //@ assert g == 0;
  return 0;
}
