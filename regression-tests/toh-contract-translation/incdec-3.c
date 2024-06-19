int a_init;
int b_init;

/*@contract@*/
void increment(int* val) {
    (*val)++;
}

/*@contract@*/
void decrement(int* val) {
    increment(val);
    *val = *val - 2;
}

int *a;

extern int non_det_int();
extern int* non_det_int_ptr();

void main()
{
  //Non-det assignment of global variables
  a_init = non_det_int();
  b_init = non_det_int();
  a = non_det_int_ptr();

  assume(1);

  a = (int*) malloc(sizeof(*a));

  *a = a_init;

  increment(a);
  decrement(a);

  assert((*a == a_init));
}
