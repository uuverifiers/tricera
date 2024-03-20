int main () {
  double a = 4.0;
  double b = 0.1;
  assert(a/b <= 40.00001);
  assert(a/b >= 39.99999);
  return 0;
}
