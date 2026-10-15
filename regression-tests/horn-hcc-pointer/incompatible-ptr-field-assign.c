struct S { char *c; };

int main() {
  int a[2];
  struct S s;
  s.c = a;
  return 0;
}
