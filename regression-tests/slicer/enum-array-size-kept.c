enum Sizes {
  CAP = 4
};

int dead_global = 99;

int main(void) {
  int arr[CAP];
  arr[0] = 10;
  arr[3] = 20;
  assert(arr[0] + arr[3] == 30);
  return 0;
}
