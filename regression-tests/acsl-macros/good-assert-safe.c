// Function-like macro used only inside an ACSL assertion (reported example).
#define GOOD(x) ((x) >= 240)

int main(void) {
  int status = 250;
  //@ assert GOOD(status);
  return 0;
}
