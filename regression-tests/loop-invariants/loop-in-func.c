/*@contract@*/
void value() {
  for (int i = 0; i < 3; ++i) {
    assert(i < 3);
  }
}
  
void foo() {
  value();
}
