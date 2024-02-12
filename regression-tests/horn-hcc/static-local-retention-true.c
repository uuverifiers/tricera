int global;

void incrementLocalStatic() {
    static int local = 0;
    local++;
    global++;
    assert(local == global);
}

void main() {
    incrementLocalStatic();
    incrementLocalStatic();
}