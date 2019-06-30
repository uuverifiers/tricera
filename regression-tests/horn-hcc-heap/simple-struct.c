struct simple{
  int x;
};

void main(){
  struct simple *p = calloc(sizeof(struct simple));
  p->x = 42;
  assert(p->x == 42 || p->x ==0);
}
