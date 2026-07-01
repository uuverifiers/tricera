// self-referential type: the reachable-type closure must terminate
struct Node {
  int val;
  struct Node *next;
};

int dead_global = 9;

int main(void) {
  struct Node n;
  n.val = 5;
  n.next = 0;
  assert(n.val == 5);
  return 0;
}
