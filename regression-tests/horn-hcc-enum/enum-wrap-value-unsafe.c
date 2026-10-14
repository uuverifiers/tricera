enum Values {
  WRAPPED = 0xffffffffU + 1U,
  NEXT
};

int main(void)
{
  assert(WRAPPED != 0);
  return 0;
}
