int global = 0;

int get_global()
{
    return global;
}

void inc_global()
{
    ++global;
}

/*@ contract @*/
int main()
{
    // ensure that preprocessor does not remove functions
    get_global();
    inc_global();
    // test begin here
    int (*f)() = get_global;
    void (*g)() = inc_global;
    int x;
    x = f();
    assert(x == 1);
    g();
    g();
    x = f();
    assert(x == 3);
}