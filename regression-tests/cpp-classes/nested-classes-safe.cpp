class Outer {
  public:
    int data;

    class Inner {
      public:
        int data;
        int get_outer(Outer *o) {
          return o->data;
        }
    };

};

int main() {
  Outer o;
  o.data = 1;
  Outer::Inner i;

  assert(i.get_outer(&o)==1);

  return 0;
}
