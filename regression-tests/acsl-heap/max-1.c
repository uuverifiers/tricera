int r;

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

/*@
  requires \true;
  ensures a_init >= b_init ==> r == a_init;
  ensures b_init > a_init ==> r == b_init;
  assigns r, a, b, *a, *b;
*/
int main(void) {
    a = (int*) malloc(sizeof(*a));
    b = (int*) malloc(sizeof(*b));

    *a = a_init;
    *b = b_init;

    r = findMax(a, b);

}
