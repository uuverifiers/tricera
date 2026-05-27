struct Node {
  struct Node* left;
  struct Node* right;
};

void main() {
  struct Node* n = malloc(sizeof(struct Node));

  n->left = 0;
  n->right = 0;

  while (n->left || n->right) {
    if (n->left)
      n = n->left;
    else
      n = n->right;
  }
}
