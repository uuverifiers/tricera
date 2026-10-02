// Macros in ACSL assertions, ghost code and \valid, all expected SAFE. Without
// expansion each annotation would be an error, so SAFE shows the expansion.
// - object-like macro, nested macros (GOOD -> LIMIT -> BASE + OFFSET)
// - ghost declaration initialiser and ghost statement
// - \valid(&arr[(N-1)]) (index parenthesised: the ACSL parser rejects arr[10-1])
#define LIMIT0 240
#define BASE 200
#define OFFSET 40
#define LIMIT (BASE + OFFSET)
#define GOOD(x) ((x) >= LIMIT)
#define INIT 5
#define STEP 2
#define N 10

int arr[10];

/*@ requires \valid(&arr[(N-1)]);
    assigns \nothing; */
void consumer(void);

int main(void) {
  int s = 240;
  //@ assert s >= LIMIT0;
  //@ assert GOOD(s);
  //@ ghost int v = INIT;
  //@ ghost v = v + STEP;
  //@ assert v == 7;
  consumer();
  return 0;
}
