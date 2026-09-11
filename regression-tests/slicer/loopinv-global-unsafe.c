// 'bound' is referenced only in the loop invariant; the pre-loop assert is the property
int dead_unused = 7;
int bound       = 3;

int main() {
  int x = 10;
  assert(x == 11);
  int i = 0;
  for (i = 0; i < 3; i++) {
    /*@ loop invariant i <= bound; @*/
    ;
  }
  return 0;
}
