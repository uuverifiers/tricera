class C {
  public:
    int *int_ptr;
    C(int* ptr) {
      int_ptr = ptr;
    }

    ~C() {
      delete int_ptr;
    }
};



int main() {
  C *c = new C(new int(5));
  delete (c);
  return 0;
}
