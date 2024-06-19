int a_init;
int b_init;

/*@contract@*/
void increment(int* val) {
    (*val)++;
}

/*@contract@*/
void decrement(int* val) {
    (*val)--;
}

int *a;
int *b;

extern int non_det_int();
extern int* non_det_int_ptr();

void main()
{
  //Non-det assignment of global variables
  a_init = non_det_int();
  b_init = non_det_int();
  a = non_det_int_ptr();
  b = non_det_int_ptr();

  assume(1);

  a = (int*) malloc(sizeof(*a));
  b = (int*) malloc(sizeof(*b));
  
  *a = a_init;
  *b = b_init;

  increment(a);
  decrement(b);

  assert(((*a == (a_init + 1)) && (*b == (b_init - 1))));
}
