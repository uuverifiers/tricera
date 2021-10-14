void main() {
  int *x = calloc(sizeof(int));
  *x += 42;
  assert(*x == 42);
  *x *= 2;
  assert(*x == 84);
  *x /= 4;
  assert(*x == 21);
  *x -= 1;
  assert(*x == 20);
  *x %= 3;
  assert(*x == 2);
}

