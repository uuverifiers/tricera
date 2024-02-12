int* invalidStackAccess() {
    int a = 10; // Local variable
    return &a;  // Returning address of local variable - leads to invalid access
}

void main() {
    int *p = invalidStackAccess();
    *p = 20; // Invalid access, dereferencing a dangling pointer
}
