struct S { int x; };
void set(int* p) { *p = 5; }
void main(void) {
  struct S v;
  v.x = 0;
  set((int*)(&v.x));
  assert(v.x == 5);
}
