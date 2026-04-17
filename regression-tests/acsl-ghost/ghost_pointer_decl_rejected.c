// Grammar accepts pointer declarators in ghost decls, but the
// backend defers their installation -- freeze the error message.
//@ ghost int *p;

int main() {
  return 0;
}
