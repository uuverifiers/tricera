int *p;

/*@contract@*/
void allocate() {
  p = malloc(sizeof(int));
  *p = 7;
}

int main() {
  allocate();
  assert(*p == 7);
  return 0;
}
