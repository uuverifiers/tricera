struct U { int x; int y; };
struct T { struct U u; int k; };

struct T t = {{1}, 5};

int main() {
  assert(t.k == 5);
  return 0;
}
