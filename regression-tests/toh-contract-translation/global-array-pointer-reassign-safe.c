int a[3], b[5]; int *p = a;
/*@ ensures p == b; */
void func() { p = b; }

// Infer a contract that uses the annotated callee's postcondition.
/*@contract@*/
void reassign() { func(); }

int main() { reassign(); assert(p == b); return 0; }
