enum E { A, B };

struct S { enum E a[2]; };

int main() {
  struct S st;
  st.a[1] = B;
  assert(st.a[1] == B);
  return 0;
}
