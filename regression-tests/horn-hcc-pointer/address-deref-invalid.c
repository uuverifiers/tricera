int main() {
    int value = 3;
    int result = &*value;
    assert(result == 3);
}
