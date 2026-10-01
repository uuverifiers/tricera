// Function-like macro used only inside an ACSL assertion (reported example).
// UNSAFE: 239 is not GOOD.
#define GOOD(x) ((x) >= 240)

int main(void) {
  int status = 239;
  //@ assert GOOD(status);
  return 0;
}
