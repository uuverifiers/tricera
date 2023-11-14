#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  
  int N = __VERIFIER_nondet_int();
  __VERIFIER_assume(N > 0);
  
  int arr[N];
  int i = 0;
  while (i < N) {
      int t = i;
      if (i % 2 == 0) {
        t = -i-1;
      }
      arr[i] = t;
      i++;
  }
  //@ assert \exists int j; ((0 <= j) && (j < N)) && (arr[j] < (3-N));
  return 0;
}
