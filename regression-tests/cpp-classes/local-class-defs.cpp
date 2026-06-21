int f(class C *x) {
  return 0;
}
int main() {

  class C {
    public:
      int f() { return 0; }
      int x;
  };

  C c;
  return 0;
}
