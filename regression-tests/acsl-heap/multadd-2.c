
void addNumbers(int* x, int* y, int* result) {
    *result = *x + *y;
}

void multiplyNumbers(int* x, int* y, int* result) {
    *result = *x * *y;
}

int* a;
int* b;
int* c;
int* result1;
int* result2;
int a_init;
int b_init;
int c_init;

/*@
  ensures *result1 == a_init + b_init;
  ensures *result2 == a_init * b_init;
  ensures *c == b_init + c_init;
  assigns a, *a, b, *b, c, *c, result1, *result1, *result2;
*/
int main(void) {
    a = (int*) malloc(sizeof(*a));
    b = (int*) malloc(sizeof(*b));
    c = (int*) malloc(sizeof(*c));
    result1 = (int*) malloc(sizeof(*result1));
    result2 = (int*) malloc(sizeof(*result2));
    *a = a_init;
    *b = b_init;
    *c = c_init;

    addNumbers(a, b, result1);
    multiplyNumbers(a, b, result2);
    addNumbers(b, c, c); 

}

