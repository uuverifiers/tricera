#include <assert.h>

extern int __VERIFIER_nondet_int(void);

void main() {
  
  int N = __VERIFIER_nondet_int();
  __VERIFIER_assume(N > 0);
  

  int arr1[N];
  int arr2[N];

  for (int i = 0; i < N; ++i) {
      arr1[i] = __VERIFIER_nondet_int();
      arr2[i] = __VERIFIER_nondet_int();
      int x = arr1[i];             // (stmt1)
      int y = 0;
      if (x >= 0)
        y = x;
      arr2[i] = y;         // (stmt2)
  }

  // int t1 = \sum(arr1, 0, N);        // (stmt3)
  // int t2 = \sum(arr2, 0, N);
  assert(\sum(arr2, 0, N) >= 0);
}
