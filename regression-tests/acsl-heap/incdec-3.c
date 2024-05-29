
int a_init;
int b_init;

void increment(int* val) {
    (*val)++;
}

void decrement(int* val) {
    increment(val);
    *val = *val - 2;
}

int *a;

/*@
  requires \true;
  ensures *a == a_init;
  assigns *a, a;
*/
int main(void) {
  a = (int*) malloc(sizeof(*a));
  
  *a = a_init;

  increment(a);
  decrement(a);

}
