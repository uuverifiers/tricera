int main() {
  int** ptr = new int*(new int(5));
  delete(*(ptr));
  delete(ptr);
  return 0;
}
