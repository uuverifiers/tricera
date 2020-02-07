struct node
{
  int x;
  //struct node *L;
  //struct node *R;
};

void main()
{
  /* initialize the doubly linked list with a single node  */
  struct node* list=calloc(sizeof(struct node));
  int y = list->x;
  assert (y != 0);
  //list->L=0;
  //list->R=0;
  //struct node *tail=list;

  /* initialize a node and add to the tail of the list */
  /*struct node *n=calloc(sizeof(struct node)); 
  n->L=tail;
  n->R=0;

  tail->R=n;*/
  /* tail=n; */

  /* the tail was not updated, the assertion should fail*/
  //assert(list != tail);
}
