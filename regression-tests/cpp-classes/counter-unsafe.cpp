#include <cassert>
class Counter {
  public:
    int value;

    Counter(int val) {
      this->value = val;
    }


    int num() {
      return 5;
    }


    void set(int val) {
      this->value = val;
    }

    void inc(){
      this->value = this->value + 1;
    }
    int get() {
      return this->value;
    }
};


int main() {

  Counter c(0);

  c.set(c.num());

  //c.value = 0;
  while (c.get() < 3) {
    c.inc();
  }

  assert(c.get() == 4);
  return 0;
}




