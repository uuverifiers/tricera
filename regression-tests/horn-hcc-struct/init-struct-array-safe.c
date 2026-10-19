struct U { int x; int y; };

int main() {
  struct U arr[2] = {{1}, {3, 4}};
  assert(arr[1].x == 3);
  return 0;
}
