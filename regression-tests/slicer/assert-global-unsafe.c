int dead_unused = 7;
int bound       = 50;

int main() {
  int x = 100;
  /*@ assert x <= bound; @*/
  return 0;
}
