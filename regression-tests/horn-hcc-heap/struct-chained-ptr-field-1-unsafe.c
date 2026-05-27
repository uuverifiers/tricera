struct Node
{
  struct Node* next;
  int data;
};

void main()
{
  struct Node* head = calloc(sizeof(struct Node));
  head->data = 3;
  head->next = calloc(sizeof(struct Node));
  head->next->next = 0;
  assert(head->data == 0);
}
