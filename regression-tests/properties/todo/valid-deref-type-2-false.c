void main() {
    long *p = (long*) malloc(sizeof(int));
    *p = 42; // Incorrect type access - accessing an 'int' as a 'long'
}
