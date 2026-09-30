enum Response {
  REJECTED = -1,
  PENDING = 0,
  ACCEPTED = 1
};

void main(void)
{
  enum Response response = REJECTED;
  assert(response == 0);
}
