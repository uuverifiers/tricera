extern int nondet();

/*$
  pre_p(int), post_p(int, int)
  $*/
int foo(int x) { // program entry point 1
  assume(pre_p(x));
  int res = x + 1;
  assert(post_p(x, res));
  return res;
}

void main1 () { // program entry point 2
  int x = _;
  int y = _;
  assert(pre_p(x));
  assume(post_p(x, y));
  assert(y == x + 1);
}

void main () {
  if (nondet())
    main1();
  else
    foo(nondet());
}
