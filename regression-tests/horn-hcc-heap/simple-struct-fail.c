struct simple{
  int x;
};

void main(){
  struct simple *p = malloc(sizeof(struct simple));
  p->x = 42;
  assert(p->x == 42); //this should actually pass after the refinements
}
