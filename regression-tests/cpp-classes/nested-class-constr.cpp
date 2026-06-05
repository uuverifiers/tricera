class A {
  public:
    int x;
    A(int val) {
      x = val;
    }


    class B {
      public:
        int y;
        B (int val) {
          y = val;
        }
    };
};

int main() {
  A a(1);
  A::B b(2);

  assert(a.x == 1 && b.y == 2);
  return 0;
}
