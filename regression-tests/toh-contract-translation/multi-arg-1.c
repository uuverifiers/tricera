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
