int i[2];

void f1() {
  assert(i[1] == (i[1] & 0x0000FFFF) + (i[1] & 0xFFFF0000));
}

void main() {
  f1();
}