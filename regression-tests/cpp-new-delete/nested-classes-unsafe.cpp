class Outer {
  public:
    int x;

    Outer(int val) {
      x = val;
    }

    ~Outer(){}

    class Inner {
      public:
        int y;

        Inner(int val) {
          y = val;
        }

        ~Inner() {}
    };
};

int main() {
  Outer::Inner *i = new Outer::Inner(1);
  Outer *o = new Outer(2);

  assert(i->y == 0 && o->x == 0);

  delete i;
  delete o;
  return 0;
}
