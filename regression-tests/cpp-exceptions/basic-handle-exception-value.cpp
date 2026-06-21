int main() {
    int x = 0;
    try {
        throw 1;
    } catch (int e) {
        x = e;
    }
 
    assert(x == 1);
    return 0;
}
