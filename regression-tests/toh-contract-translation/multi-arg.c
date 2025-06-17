/*
  NOTE: 2025-05-19: The contract currently produced is
    not the expected one. The contract produced is not
    refined enough to make the code pass e.g. Frama-C
    wp verification. The reason is that the contract
    is missing post conditions for parameter t2.
    The reason for this seems to be a limitation in
    the way TheoryOfHeapProcessor simplifies expressions.
*/

/*@contract@*/
void mod(int* t1, int* t2) {
    (*t1)++;
    (*t2)--;
}

int main() {
    int* s1 = (int*) malloc(sizeof(int));
    int* s2 = (int*) malloc(sizeof(int));

    *s1 = 1;
    *s2 = 2;

    mod(s1, s2);
    assert(*s1 == 1+1);
    assert(*s2 == 2-1);

    return 0;
}
