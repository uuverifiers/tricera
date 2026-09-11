struct S { int f; };
struct S s = { 0 };

int main() {
  /*@ ghost s.f = 5; */
  return s.f;
}
