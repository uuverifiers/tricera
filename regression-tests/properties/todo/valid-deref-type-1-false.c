void main() {
    int a = 10;
    long *p = (long *)&a;
    *p = 20; // Incorrect type access - accessing an 'int' as a 'long'
}
