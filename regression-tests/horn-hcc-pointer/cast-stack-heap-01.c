int *x = ((void *)0);
int** y = (int**)&x;

void main() {
  assert (*y == x);
}
