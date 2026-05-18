
signal p;
signal q;

int main() {
  assume(p && q);
  assert(p);
  assert(q);
}
