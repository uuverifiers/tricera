/*@contract@*/
int at_one(int n) {
  if (n == 1)
    return 2;
  return 0;
}

int main() {
  assert(at_one(1) == 2);
  return 0;
}
