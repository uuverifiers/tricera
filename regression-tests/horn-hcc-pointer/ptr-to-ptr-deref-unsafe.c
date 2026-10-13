int main() {
  int x = 1;
  int *p = &x;
  int **pp = &p;
  assert(**pp != 1);
  return 0;
}
