int main() {
  int* def_ptr = new int;
  int* val_ptr = new int();
  int* dir_ptr = new int(5);

  assert(*dir_ptr == 5);

  delete def_ptr;
  delete (val_ptr);
  delete dir_ptr;
}
