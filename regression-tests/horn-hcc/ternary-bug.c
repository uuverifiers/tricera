void main() {
  int x, y;
  int z = y;
  assume( x == ((z == y)? 1 : 0) );
  assert(0);
}
