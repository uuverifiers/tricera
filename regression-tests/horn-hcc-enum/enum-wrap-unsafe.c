enum Values {
  WRAPPED = 0xffffffffU + 1U,
  NEXT
};

void main(void)
{
  assert(WRAPPED != 0);
  assert(NEXT == 1);
}
