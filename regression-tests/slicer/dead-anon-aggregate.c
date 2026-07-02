// anonymous: always dead; appears only in the count, with no name
struct { int x; };

int main(void) {
  int y = 4;
  assert(y == 4);
  return 0;
}
