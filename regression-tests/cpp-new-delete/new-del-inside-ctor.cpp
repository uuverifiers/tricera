class C {
  public:
    int x;
    int* int_ptr;

    C(int val) {
      x = val;
      int_ptr = new int(val);
    }
    ~C() {
      delete int_ptr;
    }
};

int main() {
  C obj = C(1);

  obj.~C();

  return 0;
}
