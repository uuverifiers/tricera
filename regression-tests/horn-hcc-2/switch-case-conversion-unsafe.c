// case values are converted to the promoted selector type

int main() {
  unsigned int x = 0xFFFFFFFFu;
  int r = 0;
  switch (x) {
  case -1:
    r = 1;
    break;
  default:
    r = 2;
  }
  assert(r != 1);
  unsigned char c = 255;
  int s = 0;
  switch (c) {
  case -1:
    s = 1;
    break;
  case 255:
    s = 2;
    break;
  }
  assert(s == 2);
  return 0;
}
