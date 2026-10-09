void main() {
  unsigned u[2] = {5, -1};
  assert(u[1] > u[0]);

  int i[2] = {-1, 6};
  assert(i[0] < 0 && i[1] == 6);
}
