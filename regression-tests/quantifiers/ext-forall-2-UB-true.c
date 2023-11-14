#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  
  int N = __VERIFIER_nondet_int();
  __VERIFIER_assume(N > 0);
  

  int arr[N];
  int i = 0;
  while (i < N) {
      int t = i * i;
      arr[i] = t * t;
      i++;
  }
  //@ assert \forall int j; ((0 <= j) && (j < N)) ==> (arr[j] == (j*j*j*j));
  return 0;
}
