// regex would keep 'old' (inside '\old('); parsing the ACSL does not
int g = 0;

int old = 17;

/*@
  requires g == 0;
  ensures \result == \old(g) + 1;
*/
int inc(void) {
  g = g + 1;
  return g;
}

int main(void) {
  int r = inc();
  assert(r == 1);
  return 0;
}
