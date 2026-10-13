// without a default, a selector matching no case skips the switch body

int main() {
  int x = 2;
  int y = 0;
  switch (x) {
  case 1:
    y = 1;
    break;
  case 3:
    y = 3;
    break;
  }
  y = y + 10;
  assert(y != 10);
  return 0;
}
