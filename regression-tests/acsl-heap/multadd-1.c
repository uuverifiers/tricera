

void multiplyByTwo(int* num) {
    *num = *num * 2;
}

void addTwoNumbers(int* a, int* b, int* result) {
    *result = *a + *b;
}

int* a;
int* b;
int* result;
int a_init;
int b_init;

/*@
  requires \true;
  ensures *a == a_init * 2;
  ensures *result == *a + b_init;
  assigns a, *a, b, *b, result, *result;
*/
int main(void) {
    a = (int*) malloc(sizeof(*a));
    b = (int*) malloc(sizeof(*b));
    result = (int*) malloc(sizeof(*result));

    *a = a_init;
    *b = b_init;

    multiplyByTwo(a);
    addTwoNumbers(a, b, result);
}

