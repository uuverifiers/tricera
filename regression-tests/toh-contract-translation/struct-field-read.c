struct S {
  int x;
  int y;
};

/*@contract@*/
int f_with_arg(struct S *s) {
  return s->x + 1;
}

int entry(struct S * s)
{
  assume(s->x >= 0);

  int start_result = f_with_arg(s);

  assert(start_result == $at("Old", (int)(s->x)) + 1);
}
