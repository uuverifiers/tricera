//UNSAFE
int main() {
  double a = 2.0;
  double b = a + 0.5;
  assert(a + 0.4 == b);
}
