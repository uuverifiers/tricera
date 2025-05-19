/* 
  NOTE: 2025-03-27: Stackpointers does currently not work
    together with recursion. In a situation as the following
    the parameter gets replaced by a global variable, and the
    function is replaced by two other functions, a wrapper,
    and a transformed function that manipulates the global
    variable in a similar way to what the original function
    would do to the value pointed to by the variable. Any
    recursive call in the transformed function will call the
    wrapper but use the adress of the global variable as the
    argument. All in all, this will mess up the value of the
    global variable.
*/

/*@contract@*/ 
void incr(int* t) {
    if (*t < 5) {
      *t += 1;
      incr(t);
    }
}

int main() {
    int s = 0;
    incr(&s);
    assert(s == 5);

    return 0;
}
