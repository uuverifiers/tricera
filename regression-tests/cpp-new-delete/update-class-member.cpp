class C {
  public:
    int x;

    C(int val) {
      x = val;
    }

    ~C() {}

    void reset_x() {
      x = 0;
    }
};

int main() {
  C *obj = new C(5);

  assert(obj->x == 5);
  obj->reset_x();
  assert(obj->x == 0);

  delete obj;

  return 0;
}
