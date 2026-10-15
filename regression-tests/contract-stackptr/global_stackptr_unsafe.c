int g;
int *p = &g;

/*@
  ensures g == \old(g) + 1;
  assigns g;
*/
void inc(void) {
  g = g + 1;
}

int main(void) {
  g = 5;
  inc();
  assert(*p != 6);
  return 0;
}
