
int main() {
  clock c;
  c = 0;

  progress (c <= 5) {}
  assume(c == 5);
}
