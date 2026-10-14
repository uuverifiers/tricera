enum Values {
  WRAPPED = 0xffffffffU + 1U,
  NEXT
};

int main(void)
{
  assert(NEXT == 1);
  return 0;
}
