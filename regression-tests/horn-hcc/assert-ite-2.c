void main() {
  int x=1,y=0;
  assert((x == y ? x : y) +
         (x == y+1 ? x : y));
}
