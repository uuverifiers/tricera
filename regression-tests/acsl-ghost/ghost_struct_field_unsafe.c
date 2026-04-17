struct Point { int x; int y; };

int main() {
  /*@ ghost struct Point p;
             p.x = 3;
             p.y = 4;
  */
  //@ assert p.x == 99;
  return 0;
}
