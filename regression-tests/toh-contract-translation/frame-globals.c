int count;

/*@contract@*/
void increment(int *p) {
  ++*p;
  ++count;
}

int main() {
  int *p = malloc(sizeof(int));
  *p = 0;
  count = 0;
  increment(p);
  assert(*p == 1 && count == 1);
  return 0;
}
