// see https://github.com/uuverifiers/tricera/issues/36

void main(void) {
    int a[3];
    int b[3];

    a[0] = 42;
    b[0] = 3;

    assert(a[0] == 3); // this is not SAFE, a[0] is 42.
}