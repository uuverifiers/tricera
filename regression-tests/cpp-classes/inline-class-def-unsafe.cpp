class Global {
  public:
    int x;
    void set(int val) {
      x = val;
    }
} g;

int main() {
  class Local {
    public:
      int x;
      void set(int val) {
        x = val;
      }
  } l;

  l.set(1);
  g.set(2);

  assert(l.x == 2 && g.x == 5);
  return 0;
}
