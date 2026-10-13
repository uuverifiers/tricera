int main() {
  _Bool b = 1;
  _Bool z = 0;
  int taken = 0;
  if (b) taken = 1;
  assert(taken);
  assert(b);
  assert(!z);
  return 0;
}
