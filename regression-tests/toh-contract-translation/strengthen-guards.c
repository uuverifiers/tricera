extern int nondet();

/*@contract@*/
int positive(int x) {
  if (x > 0)
    return 1;
  return 0;
}

/*@contract@*/
int at_ten(int x) {
  if (x == 10)
    return 1;
  return 0;
}

int main() {
  int x = nondet();
  assume(x >= 0 && x <= 10);
  int a = positive(x);
  int b = at_ten(x);
  assert(a >= 0 && (x != 10 || a != 0));
  assert(b >= 0 && (x != 10 || b != 0));
}
