struct Node
{
    struct Node* next;
    int data;
};

void main()
{
    struct Node* head = calloc(sizeof(struct Node));
    assert(0 == head->next);
    // This was failing when evaluating the RHS was adding clauses.
    // E.g., when using the invariant encoding.
}