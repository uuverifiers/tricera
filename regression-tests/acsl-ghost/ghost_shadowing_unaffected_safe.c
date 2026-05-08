// A ghost `g` at file scope must not disturb a regular shadowing of
// globals by locals: `x` is global, `x` is locally shadowed in main().
//@ ghost int g;

int x;

/*@ ensures \result == 7;
*/
int main() {
  int x = 7;
  return x;
}
