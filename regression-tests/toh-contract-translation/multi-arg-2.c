/*@contract@*/
void mod(int* t1, int* t2, int* t3, int* t4) {
    (*t1)++;
    (*t3) *= 2;
    (*t2)--;
    (*t1)++;
    (*t4) = (*t1)*2;
}

int main() {
    int* s1 = (int*) malloc(sizeof(int));
    int* s2 = (int*) malloc(sizeof(int));
    int* s3 = (int*) malloc(sizeof(int));
    int* s4 = (int*) malloc(sizeof(int));

    *s1 = 1;
    *s2 = 2;
    *s3 = 3;

    mod(s1, s2, s3, s4);
    assert(*s1 == 1+1+1);
    assert(*s2 == 2-1);
    assert(*s3 == 3*2);
    assert(*s4 == 6);

    return 0;
}
