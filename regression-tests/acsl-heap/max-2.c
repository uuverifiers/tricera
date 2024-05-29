int* r;

void findMax(int* x, int* y, int* max) {
    if(*x >= *y)
        *max = *x;
    else
        *max = *y;
}

int* a;
int* b;
int a_init;
int b_init;

/*@
  requires \true;
  ensures a_init >= b_init ==> *r == a_init;
  ensures b_init > a_init ==> *r == b_init;
  assigns r, a, b, *r, *a, *b;
*/
int main(void) {
    a = (int*) malloc(sizeof(*a));
    b = (int*) malloc(sizeof(*b));
    r = (int*) malloc(sizeof(*r));

    *a = a_init;
    *b = b_init;

    findMax(a, b, r);

}
