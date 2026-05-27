/*@contract@*/
void foo() {
  for (int i = 0; i < 3; ++i) {
    assert(i < 3);
  }
}
