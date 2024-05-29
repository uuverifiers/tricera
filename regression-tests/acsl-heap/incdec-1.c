
int a_init;
int b_init;

void increment(int* val) {
    (*val)++;
}

void decrement(int* val) {
    (*val)--;
}

int *a;
int *b;
/*@
  requires \true;
  ensures *a == a_init + 1 && *b == b_init - 1;
  assigns *a, *b, a, b;
*/
int main(void) {
  a = (int*) malloc(sizeof(*a));
  b = (int*) malloc(sizeof(*b));
  
  *a = a_init;
  *b = b_init;

  increment(a);
  decrement(b);

}
