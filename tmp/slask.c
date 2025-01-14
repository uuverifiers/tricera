int func(int q) {
    {
      int q = 1;
    }
    return 0;
}

/* This syntax is not supported. '*' is considered part of the  Declarator.
   It assumes a direct_declarator following. */
void func3(double *);

int func2(int *) {
  return 0;
}

int main() {
    return 0;
}