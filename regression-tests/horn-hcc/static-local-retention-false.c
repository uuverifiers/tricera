void incrementLocalStatic() {
    static int local = 0;
    assert(local == 0); // Will fail in second call.
    local++;
}

void main() {
    incrementLocalStatic();
    incrementLocalStatic();
}