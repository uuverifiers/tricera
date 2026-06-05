class C {
  public:
    int x;
    int *int_ptr;
    C(int val) {
      x = val;
      int_ptr = malloc(sizeof(int));
    }

    ~C() {
      free(int_ptr);
    }
};

class C2 {
  public:
    int y;
    int *int_ptr;
    C2(int val, int *ptr) {
      y = val;
      int_ptr = ptr;
    }
    ~C2() { free(int_ptr); }
};




int main() {
  class C assign_ctor = C(1);
  C inline_ctor(2);

  assert(assign_ctor.x == 1);
  assert(inline_ctor.x == 2);

  assign_ctor.~C();
  inline_ctor.~C();

  C2 c2 = C2(1, malloc(sizeof(int)));
  c2.~C2();

  //int *i = malloc(sizeof(int));
  return 0;
}
