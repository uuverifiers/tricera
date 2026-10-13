_Bool identity(_Bool b) { return b; }
_Bool intToBool(int v) { return v; }

int main() {
  int v = 5;
  assert(identity(v) == 1);
  assert(intToBool(v) == 1);
  return 0;
}
