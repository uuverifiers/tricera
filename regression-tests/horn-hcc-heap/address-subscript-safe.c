int main() {
    int a[2] = {1, 2};
    int *end = &a[2];
    assert(end == a + 2);
    assert(&2[a] == end);

    int i = 0;
    int *p = &a[i++];
    assert(i == 1 && *p == 1);
    int *q = &(p++)[0];
    assert(q == a && p == a + 1);
}
