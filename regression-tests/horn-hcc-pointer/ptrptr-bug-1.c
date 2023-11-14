void main(void) {
  int** p = (int**) malloc(sizeof *p); // this was a bug from tri-pp
  *p = 0;
}
