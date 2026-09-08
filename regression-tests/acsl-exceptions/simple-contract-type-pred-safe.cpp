/*@
    requires \true;
    ensures \result == 1;
    throws { int } n < 0;
*/
int f(int n) {
    if (n < 0) {
        throw 10;
    }
    return 1;
}

int main() {
    int x = 0;
    try {
        x = f(0);
    } catch (int) {}
    assert(x == 1);
    return 0;
}