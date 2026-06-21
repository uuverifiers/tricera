#include <cassert>

class Accumulator {
  public:
    int total;
    int updates;

    Accumulator(int init) {
      this->total = init;
      this->updates = 0;
    }

    void add(int v) {
      this->total = this->total + v;
      this->updates = this->updates + 1;
    }

    void reset(int v) {
      this->total = v;
      this->updates = 0;
    }

    int getTotal() {
      return this->total;
    }

    int getUpdates() {
      return this->updates;
    }
};


class Multiplier {
  public:
    int factor;

    Multiplier(int f) {
      this->factor = f;
    }

    int apply(int x) {
      return x * this->factor;
    }

    void changeFactor(int f) {
      this->factor = f;
    }

    int getFactor() {
      return this->factor;
    }
};


class Controller {
  public:
    int threshold;

    Controller(int t) {
      this->threshold = t;
    }

    void process(Accumulator* acc, Multiplier* mul) {
      while (acc->getTotal() < this->threshold) {
        int value = mul->apply(1);
        acc->add(value);
      }
    }

    void adjustThreshold(int delta) {
      this->threshold = this->threshold + delta;
    }

    int getThreshold() {
      return this->threshold;
    }

};

int test(int val) {
  return val;
}

int main() {

  Accumulator acc(0);
  Multiplier mul(2);
  Controller ctrl(10);


  ctrl.process(&acc, &mul);

  assert(acc.getTotal() >= 10);
  assert(acc.getUpdates() > 0);

  int firstTotal = acc.getTotal();
  int firstUpdates = acc.getUpdates();

  mul.changeFactor(3);

  ctrl.adjustThreshold(5);
  ctrl.process(&acc, &mul);

  assert(acc.getTotal() >= 15);
  assert(acc.getTotal() >= firstTotal);

  int secondTotal = acc.getTotal();
  int secondUpdates = acc.getUpdates();

  assert(secondUpdates > firstUpdates);

  acc.reset(1);
  assert(acc.getTotal() == 1);
  assert(acc.getUpdates() == 0);

  while (acc.getTotal() < 7) {
    acc.add(1);
  }

  assert(acc.getTotal() == 7);
  assert(acc.getUpdates() == 6);

  return 0;
}
