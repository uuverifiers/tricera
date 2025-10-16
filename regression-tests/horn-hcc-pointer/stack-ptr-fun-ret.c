int x, y;
extern int nondet();

int *get_stack_ptr()
{
    return (nondet() ? &x : &y);
}

void main()
{
    int *p = get_stack_ptr();
    assert(*p == 0); //safe ,but we do not yet support getting stack pointers this way.
}
