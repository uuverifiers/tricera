
void main() {
    int *x = calloc(sizeof(int));
    *x = 42;
    *x = 3;
    int y = *x + *x;
    assert(y == 7);
}
