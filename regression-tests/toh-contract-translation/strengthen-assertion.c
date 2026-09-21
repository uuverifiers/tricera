/*@contract@*/
int positive(int n) {
    assert(n > 0);
    return n;
}

int main() {
    assert(positive(1) == 1);
}
