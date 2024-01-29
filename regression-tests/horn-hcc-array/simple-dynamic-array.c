int a[];

void main() {
  a = malloc(sizeof(int)*(2));
  a[0] = 1;
  a[1] = 2;
  assert((a[0] + a[1]) == 3);
  free(a);
}
