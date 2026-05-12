/*@ 
    requires \true;
*/
void g() {
    throw 10;
}

/*@
    requires \true;
    ensures \result == 1;
    throws \true;
*/
int f() {
    g();
    return 1;
}

int main() {
    int x = 0;
    try {
        x = f();
    } catch (int e) {
        x = e;
    }
    return 0;
}
