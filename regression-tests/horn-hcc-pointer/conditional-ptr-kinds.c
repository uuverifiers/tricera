extern int __VERIFIER_nondet_int(void);
int main() {
  int x = 0;
  int arr[2] = {0, 0};
  int *p = __VERIFIER_nondet_int() ? &x : arr;
  *p = 7;
  assert(x == 7 || arr[0] == 7);
  return 0;
}
