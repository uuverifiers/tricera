struct DivByZeroErr {};

int div(int a, int b) {
    if (b == 0) {
        struct DivByZeroErr err;
        throw err;
    }
    return a / b;
}

int main() {
    int x;
    try {
        x = div(10, 0);
    } catch (struct DivByZeroErr) {
        x = -1;
    }
    assert(x == -1);
    return 0;
}