enum Values {
  NEGATIVE = -(1 + 2),
  NEXT,
  POSITIVE = 3 * (NEXT + 4),
  MINIMUM = -2147483647 - 1
};

void main(void)
{
  assert(NEGATIVE == -3);
  assert(NEXT == -2);
  assert(POSITIVE == 6);
  assert(MINIMUM == -2147483647 - 1);
}
