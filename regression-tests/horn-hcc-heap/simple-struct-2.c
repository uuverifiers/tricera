typedef struct {
  int x;
  struct {
    int z;
  }y;
} S;

void main(){
  S *p = calloc(sizeof(S)); 

  p->y.z = 42;

  assert(p->y.z == 0 || p->y.z==42);

}
