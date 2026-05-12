/*@
    requires \true;
*/
int f() {
    throw 10;
}

int main() {
    int x = 0;
    try {
        x = f();
    } catch (int) {}
    return 0;
}