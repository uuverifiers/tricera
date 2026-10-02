// The expansion of CLOSE contains "*/", which would end the block comment
// early, so tri-pp keeps the annotation verbatim. TriCera reports this
// instead of verifying the program.
#define CLOSE "*/"

int main(void) {
  char *s = "a";
  /*@ assert s != CLOSE; */
  return 0;
}
