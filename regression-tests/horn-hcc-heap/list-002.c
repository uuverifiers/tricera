typedef enum {false, true} _Bool;

_Bool nondet_bool(void);

struct node
{
  struct node *L;
  struct node *R;
};

void main()
{
  _Bool listNotEmpty = false;
  struct node* list=malloc(sizeof(struct node));
  list->L=0;
  list->R=0;

  struct node *tail=list;

  while(nondet_bool())
  {
    struct node *n=malloc(sizeof(struct node)); 
    if(n==0)
      break;
    n->L=tail;
    n->R=0;
    tail->R=n;
    tail=n;

    listNotEmpty = true;
  }

  if(listNotEmpty)
    assert(list != tail);
}
