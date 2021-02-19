void foo() {
  malloc(sizeof(int));
}

int main() {
  foo();
  return 0;
}
