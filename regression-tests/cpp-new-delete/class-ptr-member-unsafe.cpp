class C {
  public:
    int* int_ptr;

    C(int* ptr) {
      int_ptr = ptr;
    }

    ~C() {
      delete int_ptr;
    }
};

int main() {
  C *obj = new C(new int(0));

  assert(*(obj->int_ptr) == 1);

  delete obj;

  return 0;
}
