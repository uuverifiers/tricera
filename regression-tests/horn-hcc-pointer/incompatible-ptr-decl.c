struct A { int tag_A; };
struct B { int tag_B; };

void main() {
  struct B b;
  b.tag_B = 2;
  struct A *a = &b;
  assert(a->tag_B == 2);
}
