class C {
  public:
    int *int_ptr;
    C(int *ptr) {
      int_ptr = ptr;
    }

    ~C() { free(int_ptr); }
};

int main() {
  C c(calloc(sizeof(int)));
  return 0;
};
