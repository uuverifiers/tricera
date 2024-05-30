int r;

/*@contract@*/
int findMax(int* x, int* y) {
    if(*x >= *y)
        return *x;
    else
        return *y;
}

int* a;
int* b;
int a_init;
int b_init;

extern int non_det_int();
extern int* non_det_int_ptr();

void main()
{
  //Non-det assignment of global variables
  r = non_det_int();
  a = non_det_int_ptr();
  b = non_det_int_ptr();
  a_init = non_det_int();
  b_init = non_det_int();

  assume(1);

  a = (int*) malloc(sizeof(*a));
  b = (int*) malloc(sizeof(*b));

  *a = a_init;
  *b = b_init;

  r = findMax(a, b);

  assert(!((a_init >= b_init) && !(r == a_init)));
  assert(!((b_init > a_init) && !(r == b_init)));
}
