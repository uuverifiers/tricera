void main() {
  int n = 3;
  int a[];
  int i = 0;
  for(; i < n; ++i) 
  {
    a[i] = i-1;
  }

  //@  assert \exists int j; (((0 <= j) && (j < n)) && (a[j] == 1));
}
