
void main(void) {
  int b[_]; // cell contents unknown

  assume(1); // {Q : T}

  int i = 1, s = b[0];

  while (i < 11) {
    s += b[i];
    i += 1;
  }

  //i = 1;

  assert(s == \sum(b, 0, 11));

  //assert(s == (b[0] + b[1] + b[2] + b[3] + b[4] +
  //             b[5] + b[6] + b[7] + b[8] + b[9] +
  //             b[10]));
}

