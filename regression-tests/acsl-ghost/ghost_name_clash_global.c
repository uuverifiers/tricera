// A ghost variable may not share its name with a regular C variable.
// Expect a declaration-time error, not SAFE/UNSAFE.
//@ ghost int v;
int v;

int main() { return 0; }
