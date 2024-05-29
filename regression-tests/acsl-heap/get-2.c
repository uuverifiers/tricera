
int r1;
int n_init;


int get(int* p) {
    if (*p <= 0) {
        return 0;
    } else {
        *p = *p - 1;
        return 1 + get(p);
    }
}

int* n;
/*@
  requires n_init > 0;
  ensures r1 >= n_init && r1 <= n_init * n_init;
  assigns r1, n, *n;
*/
int main(void) {
    n = (int*) malloc(sizeof(*n));

    *n = n_init;

    r1 = get(n);
}
