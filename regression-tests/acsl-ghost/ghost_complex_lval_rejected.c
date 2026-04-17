// Grammar accepts complex lvalues but the backend rejects them with
// a clear error. This is the lvalue-deferred path; freezing it here
// ensures the deferral is well-signalled to users.
//@ ghost int v;

int main() {
  //@ ghost *v = 1;
  return 0;
}
