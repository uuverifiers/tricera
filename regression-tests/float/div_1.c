int main () {
  float a = 4.0f;
  float b = 0.1f;
  assert(a/b <= 40.00001f);
  assert(a/b >= 39.99999f);
  return 0;
}
