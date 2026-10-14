int main() {
  assert(-1 + 0u != 4294967295u);
  assert(-1 + 0ul > 0);
  assert(-1 / 42u == 102261126u);
  return 0;
}
