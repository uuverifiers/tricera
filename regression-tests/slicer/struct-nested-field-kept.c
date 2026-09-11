struct Inner {
  int v;
};

struct Outer {
  struct Inner in;
  int tag;
};

int dead_global = 99;

int main(void) {
  struct Outer o;
  o.in.v = 5;
  o.tag = 1;
  assert(o.in.v == 5);
  return 0;
}
