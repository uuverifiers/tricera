struct node {
  struct node *next;
  int data;
};

void main() {
  struct node *head = calloc(sizeof(struct node));
  head->data = 1;
  head->next = 0;

  struct node *n = calloc(sizeof(struct node));
  n->data = 2;
  n->next = 0;
  head->next = n;

  assert(head->data == 2);
}
