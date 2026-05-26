
int x1;
int y1;

signal p1;
signal p2;

thread Observer {
  int x = -42;
  assert(p1); // UNSAFE
}
