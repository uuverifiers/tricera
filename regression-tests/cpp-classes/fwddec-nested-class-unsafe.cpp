#include <cassert>

class Outer {
  public:
    int x;
    class Inner {
      public:
        int y;
        int f_no_args();
        int f_args(int x);
    };
};

int Outer::Inner::f_no_args() {
  return 0;
}

int Outer::Inner::f_args(int x) {
  return x;
}


int main() {
  Outer::Inner obj;

  assert(obj.f_no_args() == 2);
  assert(obj.f_args(1) == 5);

  return 0;
}
