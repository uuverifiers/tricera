void swap(int *x, int *y){
    int tmp = *x;
    *x = *y;
    *y = tmp; 
}

void main() {
    int *a = calloc(sizeof(int));
    *a = 3;
    int *b = calloc(sizeof(int));
    *b = 42;
    swap(a, b);
    int z = *a;
    assert(*a == 0 || z == 3 || z == 42);
}

