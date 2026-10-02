/*@
  requires \valid(p);
  ensures *p == 0;
  assigns *p;
*/
extern void reset(int* p);

/*@ contract */
int f(int x) {
    return x + 1;
}

int main(void) {
    int a = 5;
    reset(&a);
    int y = f(3);
    assert(y == 4 && a == 0);
    return 0;
}
