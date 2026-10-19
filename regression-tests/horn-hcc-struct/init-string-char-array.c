struct C { char c[4]; int k; };

int main() {
  struct C v = {"ab", 1};
  assert(v.k == 1);
  return 0;
}
