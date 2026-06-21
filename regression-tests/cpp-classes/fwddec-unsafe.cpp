#include <cassert>

class C {
  public:
  int data;
  int fun_no_args();
  int fun_args(int x);
};

int C::fun_no_args() {
  this->data = 1;
  return this->data;
}

int C::fun_args(int x) {
  return x;
}

int main() {
  C c_obj;

  c_obj.fun_no_args();
  assert(c_obj.fun_no_args() == 1);

  assert(c_obj.fun_args(0) == 5);

  return 0;
}
