int* validStackAccess() {
    static int a = 10; // Static variable persists beyond the scope of the function
    return &a;
}

void main() {
    int *p = validStackAccess();
    *p = 20; // Valid access
}
