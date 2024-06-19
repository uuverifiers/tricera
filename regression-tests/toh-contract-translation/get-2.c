// TODO: This test currently results in 
//
// java.lang.Exception: Predicate generation failed
// (error "Predicate generation failed")
// Other Error: Predicate generation failed
// 
// 
int r1;
int n_init;


int get(int* p) {
    if (*p <= 0) {
        return 0;
    } else {
        *p = *p - 1;
        return 1 + get(p);
    }
}

int* n;

extern int non_det_int();
extern int* non_det_int_ptr();

void main()
{
  //Non-det assignment of global variables
  r1 = non_det_int();
  n_init = non_det_int();
  n = non_det_int_ptr();

  assume((n_init > 0));

  n = (int*) malloc(sizeof(*n));
  // Commenting out the following line makes the test pass,
  // but leads to undefined behavior. 
  *n = n_init;
  r1 = get(n);

  assert(((r1 >= n_init) && (r1 <= (n_init * n_init))));
}
